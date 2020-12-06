#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;


typedef std::map<Symbol, CallDecl> CallTable;
CallTable callTable;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol
        Int,
        Float,
        String,
        Bool,
        Void,
        Main,
        print
;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic
    analysis in a recursive way.
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    int cnt = 0;
    for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
        Decl tmp_decl = decls->nth(i);
        if (tmp_decl->isCallDecl()) {
            CallDecl call = static_cast<CallDecl>(tmp_decl);
            if (strcmp(call->getName()->get_string(), "printf") == 0) {
                semant_error(tmp_decl) << "Function printf cannot be redefination.\n";
                semant_error(tmp_decl) << "Function printf cannot have a name as printf.\n";
            }
            else if (callTable.find(tmp_decl->getName()) != callTable.end())
                semant_error(tmp_decl) << "Function " << tmp_decl->getName() << " was previously defined.\n";
            else {
                callTable[tmp_decl->getName()] = call;
                cnt++;
            }
        }
    }
    if (semant_debug) cout << "Debug msg: Install " << cnt << "callDecls." << endl;
}

static void install_globalVars(Decls decls) {
    int cnt = 0;
    for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
        Decl tmp_decl = decls->nth(i);
        if (!tmp_decl->isCallDecl()) {
            VariableDecl variableDecl = static_cast<VariableDecl>(tmp_decl);
            if (objectEnv.lookup(variableDecl->getName()) != NULL)
                semant_error(variableDecl) << "var " << variableDecl->getName()->get_string() << " was previously defined.\n";
            else {
                objectEnv.addid(variableDecl->getName(), new Symbol(variableDecl->getType()));
                ++cnt;
            }
        }
    }
    if (semant_debug) {
        std::cout << "Debug msg: Install " << cnt << "globalVarDecls.\n" << std::endl;
    }
}

static void check_calls(Decls decls) {
    if (semant_debug) cout << "---check_calls---" << endl;
    for (CallTable::iterator it = callTable.begin(); it != callTable.end(); it++) {
        it->second->check();
    }
}

static void check_main() {
    if (callTable.find(Main) == callTable.end()) {
        semant_error() << "Main function is not defined.\n";
        return;
    }

    curr_decl = callTable[Main];


    CallDecl main = static_cast<CallDecl>(curr_decl);
    if (main->getVariables()->len() != 0) {
        semant_error(curr_decl) << "Main function should not have any parameters.\n";
    }

    if (curr_decl->getType() != Void)
        semant_error(curr_decl) << "Main function should have return type Void.\n";
}

void VariableDecl_class::check() {
    if (semant_debug) cout << "---VariableDecl_class---" << getName() << endl;

    if (!isValidTypeName(variable->getType()))
        semant_error(this) << "var " << variable->getName() << " cannot be of type Void. Void can just be used as return type.\n";
    else if (objectEnv.probe(variable->getName()) != NULL)
        semant_error(this) << "redifined.";
    else
        objectEnv.addid(getName(), new Symbol(getType()));
}

void CallDecl_class::check() {
    if (semant_debug) cout << "---CallDecl_class::check---" << this->getName() << endl;

    if (!isValidCallName(getType()))
        semant_error(this) << "ReturnType can not be print.\n";

    objectEnv.enterscope();
    Variables params = getVariables();
    for (int i = params->first(); params->more(i); i = params->next(i)) {
        Variable param = params->nth(i);
        if (semant_debug) cout << "---CallDecl_class---param_name---" << param->getName() << endl;
        bool flag1 = true, flag2 = true;
        if (param->getType() == Void) {
            semant_error(this) << "Function " << getName() << " 's parameter has an invalid type Void.\n";
            flag1 = false;
        }
        if (objectEnv.probe(param->getName()) != NULL && *(objectEnv.probe(param->getName())) == param->getType()) {
            semant_error(this) << "Function " << getName() << " 's parameter has a duplicate name " << param->getName() << ".\n";
            flag2 = false;
        }
        if (flag1 && flag2)
            objectEnv.addid(param->getName(), new Symbol(param->getType()));
    }

    getBody()->check(getType());

    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    if (semant_debug) cout << "---StmtBlock_class::check---" << endl;
    objectEnv.enterscope();
    VariableDecls localVarDecls = getVariableDecls();
    for (int i = localVarDecls->first(); localVarDecls->more(i); i = localVarDecls->next(i)) {
        VariableDecl localVarDecl = localVarDecls->nth(i);
        if (semant_debug) cout << "---StmtBlock_class::check---localVarDecl->getName()---" << localVarDecl->getName() << " ";
        localVarDecl->check();
    }
    if (semant_debug) cout << endl;
    Stmts localStmts = getStmts();
    if (semant_debug) cout << "---StmtBlock_class::check---localStmts->len()---" << localStmts->len() << endl;
    Stmt localStmt;
    for (int i = localStmts->first(); localStmts->more(i); i = localStmts->next(i)) {
        localStmt = localStmts->nth(i);
        localStmt->check(type);
    }
    objectEnv.exitscope();
}

void IfStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---IfStmt_class---" << endl;

    getCondition()->checkType()->get_string();
    if (getCondition()->checkType() != Bool)
        semant_error(this) << "Predicate of 'if' does not have type Bool.\n";
    objectEnv.enterscope();
    getThen()->check(type);
    getElse()->check(type);
    objectEnv.exitscope();
}

void WhileStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---WhileStmt_class---" << endl;

}

void ForStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---ForStmt_class---" << endl;

}

void ReturnStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---ReturnStmt_class---" << endl;

}

void ContinueStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---ContinueStmt_class---" << endl;

}

void BreakStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---BreakStmt_class---" << endl;

}

Symbol Call_class::checkType(){
    if (semant_debug) cout << "---Call_class---" << name << endl;

    if (callTable.find(name) == callTable.end()){
        if (strcmp(name->get_string(), "printf")){
            if (!sameType(actuals->nth(0)->checkType(), String)){
                semant_error(this) << "the first of print should be string" << endl;
            }
            return Void;
        }
        semant_error() << "noname" <<endl;
        return Void;
    }

    Variables variables1 = callTable[name]->getVariables();
    Actuals actuals1 = actuals;
    if (variables1->len() != actuals1->len()) {
        semant_error(this) << "Function " << name << " called with wrong number of arguments.\n";
        return callTable[name]->getType();
    }
    for (int i = variables1->first(); variables1->more(i); i = variables1->next(i)) {
        if (variables1->nth(i)->getType() != actuals1->nth(i)->checkType())
            semant_error(this) << "Function " << name << " , the " << i << " parameter should be " << variables1->nth(i)->getType() << " but provided a " << actuals1->nth(i)->getType() << ".\n";
    }
    if (semant_debug) cout << "---callTable[name]->getType():" << callTable[name]->getType()->get_string() << endl;
    return callTable[name]->getType();
}

Symbol Actual_class::checkType(){
    if (semant_debug) cout << "---Actual_class---" << endl;

    Symbol type = expr->checkType();
    setType(type);
    return type;
}

Symbol Assign_class::checkType(){ // expr
    if (semant_debug) cout << "---Assign_class---" << lvalue->get_string() << endl;

    if (objectEnv.lookup(lvalue) == NULL) {
        semant_error(this) << "Left value " << lvalue << " has not been defined.\n";
        return Void;
    }

    Symbol actualType = value->checkType();
    Symbol expectedType = *(objectEnv.lookup(lvalue));
//    semant_error() << "actualType:" <<actualType->get_string() << endl;
    if (!sameType(expectedType, actualType)) {
        semant_error(this) << "Right value must have type " << expectedType->get_string() << " , got " << actualType->get_string() << ".\n";
    }
    return expectedType;
}

Symbol Add_class::checkType(){
    if (semant_debug) cout << "---Add_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Add_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Add_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Minus_class::checkType(){
    if (semant_debug) cout << "---Minus_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Minus_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Minus_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Multi_class::checkType(){
    if (semant_debug) cout << "---Multi_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Multi_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Multi_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Divide_class::checkType(){
    if (semant_debug) cout << "---Divide_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Divide_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Divide_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Mod_class::checkType(){ // %
    if (semant_debug) cout << "---Mod_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int)|| !sameType(type2, Int)) {
        semant_error(this) << "Cannot mod a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Mod_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Mod_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Neg_class::checkType(){ // -
    if (semant_debug) cout << "---Neg_class---" << endl;

    Symbol type1 = e1->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float)) {
        semant_error(this) << "A " << type1 << " doesn't have a negative.\n";
        if (semant_debug) cout << "---Neg_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Neg_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Lt_class::checkType(){ // <
    if (semant_debug) cout << "---Lt_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Lt_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Lt_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Le_class::checkType(){ // <=
    if (semant_debug) cout << "---Le_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Le_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Le_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Equ_class::checkType(){ // ==
    if (semant_debug) cout << "---Equ_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) && !sameType(type1, Bool) || !sameType(type2, Int) && !sameType(type2, Float) && !sameType(type2, Bool)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Equ_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Equ_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Neq_class::checkType(){ // !=
    if (semant_debug) cout << "---Neq_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) && !sameType(type1, Bool) || !sameType(type2, Int) && !sameType(type2, Float) && !sameType(type2, Bool)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Neq_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Neq_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Ge_class::checkType(){ // >=
    if (semant_debug) cout << "---Ge_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Ge_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Ge_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Gt_class::checkType(){ // >
    if (semant_debug) cout << "---Gt_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float) || !sameType(type2, Int) && !sameType(type2, Float)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Gt_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Gt_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol And_class::checkType(){
    if (semant_debug) cout << "---And_class---" << endl;

}

Symbol Or_class::checkType(){
    if (semant_debug) cout << "---Or_class---" << endl;

}

Symbol Xor_class::checkType(){
    if (semant_debug) cout << "---Xor_class---" << endl;

}

Symbol Not_class::checkType(){
    if (semant_debug) cout << "---Not_class---" << endl;

}

Symbol Bitand_class::checkType(){
    if (semant_debug) cout << "---Bitand_class---" << endl;

}

Symbol Bitor_class::checkType(){
    if (semant_debug) cout << "---Bitor_class---" << endl;

}

Symbol Bitnot_class::checkType(){
    if (semant_debug) cout << "---Bitnot_class---" << endl;

}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if (semant_debug) cout << "---Object_class---" << var << endl;

    if (!objectEnv.lookup(var)) {
        semant_error(this) << "object " << var << " has not been defined.\n";
        return Void;
    }
    else
        return *(objectEnv.lookup(var));
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    semant_debug = 1;
    initialize_constants();
    install_calls(decls);
    check_main();
    objectEnv.enterscope();
    install_globalVars(decls);
    check_calls(decls);
    objectEnv.exitscope();

    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



