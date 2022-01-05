package main

func f() int {}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/return/no_return.go", line 3, characters 5-6:
error: missing return at end of function f
*/
