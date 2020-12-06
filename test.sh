#!/bin/bash
filename=$1
echo "--------Make---------"
make
echo "--------Test using" $filename "--------"
echo "---semant---"
./semant $filename > output.txt
echo
echo "---semant_answer---"
./semant_answer $filename > output_answer.txt
diff output.txt output_answer.txt > /dev/null
if [ $? -eq 0 ] ; then
    echo passed
else
    echo NOT passed
fi