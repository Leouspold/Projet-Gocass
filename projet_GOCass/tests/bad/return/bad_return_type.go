package main

func foo() (int, int) {
	return 42, "Hello"
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/return/bad_return_type.go", line 3, characters 5-8:
error: bad return type int, string, expected int, int in function foo
*/
