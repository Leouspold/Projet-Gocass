package main

func f(a int, a int) {}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/func/multiple_param_func_def.go", line 3, characters 7-8:
error: duplicate parameter a in function f
*/
