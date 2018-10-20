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

let
  testnum = 0
  global tnum
  tnum() = testnum += 1
end

push!(LOAD_PATH, pwd())

using Lexer
using Error

function testNum(num)
  return string(num) * ". "
end

function parseT(str)
  TransInt.parse(Lexer.lex(str))
end

function analyze(str)
  TransInt.analyze(parseT(str))
end

function interpret(str)
  TransInt.calc(analyze(str))
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

function testContains(f, param, reg, num)
  try
    answer = string(occursin(reg, removeNL(f(param))))
    println(testNum(num) * answer)
  catch Y
    println(testNum(num) * removeNL(Y))
  end
end


testPass(parseT, "(and 1 2 3 3)", tnum())
testPass(parseT, "(and (and 1 2) a)", tnum())
testPass(parseT, "(+ 1 2 3 4)", tnum())
testPass(parseT, "(+ (+ 1 2 3) 2)", tnum())

testContains(analyze, "(with ((x 1)) x)", r"with", tnum())
testContains(analyze, "(and 1 2 3)", r"And", tnum())

testAns(interpret, "(and 1 2)", tnum())
testAns(interpret, "(+ 1 2 3)", tnum())
testAns(interpret, "(* (and 1 2 3) (+ 1 2 3))", tnum())
"""
    tests_info = """1. 1 point. Pass parse Test (and 1 2 3 3)
2. 1 point. Pass parse Test (and (and 1 2) a)
3. 1 point. Pass Parse Test  (+ 1 2 3 4)
4. 1 point. Pass Parse Test  (+ (+ 1 2 3) 2)
5. 1 point. false Analyze Test (with ((x 1)) x)"
6. 1 point. false Analyze Test (and 1 2 3)
7. 1 point. Main.TransInt.NumVal(1) Calc Test (and 1 2)
8. 1 point. Main.TransInt.NumVal(6) Calc Test (+ 1 2 3)
9. 1 point. Main.TransInt.NumVal(6) Calc Test (* (and 1 2 3) (+ 1 2 3))
"""
    correctoutput = """1. Pass
2. Pass
3. Pass
4. Pass
5. false
6. false
7. Main.TransInt.NumVal(1)
8. Main.TransInt.NumVal(6)
9. Main.TransInt.NumVal(6)
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
