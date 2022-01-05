package main

func f(a int) A {}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/func/unknown_return_value_func_type.go", line 3, characters 5-6:
error: undefined type A of one of return values in function f
*/
