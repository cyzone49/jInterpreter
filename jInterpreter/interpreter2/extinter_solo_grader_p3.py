# example: run this with "python grader_filename.py your_code_filename"
# this is an auto-generated file for general student testing

import sys
import subprocess
import os
from difflib import Differ
if __name__ == "__main__":
    fn = sys.argv[1]
    tmp_fn = "tmp.rkt"
    feedback_fn = "feedback.txt"
    run_cmd = "julia"
    tests = """

push!(LOAD_PATH, pwd())

using Lexer
using Error

let
	testnum = 0
	global tnum
	tnum() = testnum += 1
end
function testNum(num)
  return string(num) * ". "
end

function parseT(str)
  ExtInt.parse(Lexer.lex(str))
end

function interpretT(str)
  ExtInt.calc(parseT(str))
end

function removeNL(str)
replace(string(str), "\n" => "")
end

function testErr(f, param, num)
  try
    println(testNum(num) *  removeNL(f(param)))
  catch Y
    if (typeof(Y) != Error.LispError)
      println(testNum(num) * removeNL(Y))
    else
      println(testNum(num) * "Error")
    end
  end
end

function testPass(f, param, num)
  try
    f(param)
    println(testNum(num) * "Pass")
  catch Y
    println(testNum(num) * removeNL(Y))
  end
end

function testAns(f, param, num)
  try
    println(testNum(num) *  removeNL(f(param)))
  catch Y
    println(testNum(num) * removeNL(Y))
  end
end


testPass(parseT, "(+ 1 (- 3 4))", tnum()) # Pass RudInt
testErr(parseT, "(-)", tnum()) # Error
testErr(parseT, "if0", tnum()) # Error
testAns(interpretT, "(if0 1 2 3)", tnum()) #Pass
testAns(interpretT, "(with ((x 1)) x)", tnum()) # Pass
testPass(interpretT, "(lambda (x) x)", tnum()) # Pass
testPass(parseT, "(1 2 3)", tnum()) #Pass
testErr(interpretT, "(+ (lambda (x) x) 2)", tnum()) #Error
testErr(interpretT, "(collatz -1)", tnum()) #Error
testAns(interpretT, "((lambda () 4))", tnum()) # numval 4
"""
    tests_info = """1. 1 point. parse (+ 1 (- 3 4)), nested expressions
2. 1 point. parse (-) Be sure to check arguments
3. 1 point. parse if0, Don't use Key words as id's
4. 1 point. calc (if0 1 2 3), Make sure your If statements work
5. 1 point. calc (with ((x 1)) x), Make sure your withs work
6. 1 point. calc (lambda (x) x), Make sure your lambdas parse and calc
7. 1 point. parse (1 2 3), Not a parse error,
8. 1 point. calc (+ (lambda (x) x) 2), make sure to check your types
9. 1 point. calc (collatz -1), Don't allow invalid arithmatic
10. 1 point. calc ((lambda () 4)), Function application
"""
    correctoutput = """1. Pass
2. Error
3. Error
4. Main.ExtInt.NumVal(3)
5. Main.ExtInt.NumVal(1)
6. Pass
7. Pass
8. Error
9. Error
10. Main.ExtInt.NumVal(4)
"""
    grade = 0
    total_possible = 0
    with open(fn, "r") as f:
        with open(tmp_fn, "w") as w:
            w.write(f.read())
            w.write(tests)
    cmd = [run_cmd, tmp_fn]
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE)
    studentoutput, err = process.communicate()
    studentoutput = studentoutput.decode('utf-8')
    comparison = "".join(Differ().compare(correctoutput.splitlines(1), studentoutput.splitlines(1)))
    error_line_nos = []
    extra_line_nos = []
    q_line_nos = []
    for count, i in enumerate(comparison.splitlines()):
        if "-" == i[0]:
            error_line_nos.append(count)
        elif "+" == i[0]:
            extra_line_nos.append(count)
        elif "?" == i[0]:
            q_line_nos.append(count)
    failed_tests_line_nos = []
    for x in error_line_nos:
        numextralines = len([y for y in extra_line_nos if y < x])
        numqlines = len([z for z in q_line_nos if z < x])
        failed_tests_line_nos.append(x - numextralines - numqlines)
    with open(feedback_fn, "w") as feedback_file:
        feedback_file.write("        Correct output:\n")
        feedback_file.write(str(correctoutput))
        feedback_file.write("\n        Your output:\n")
        feedback_file.write(str(studentoutput))
        feedback_file.write("\n        Failed tests:\n")
        for count, l in enumerate(tests_info.splitlines(1)):
            points = int(l.split()[1])
            if count in failed_tests_line_nos:
                total_possible += points
                feedback_file.write(l)
            else:
                total_possible += points
                grade += points
        feedback_file.write("\n        Grade:\n" + str(grade) + " out of " + str(total_possible))
    os.remove(tmp_fn)
    print("See feedback file: " + feedback_fn)
