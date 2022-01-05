package main

func foo() (int, string) {
	return 12, "Hello"
}

func bar(a int, b int, c int) int {
	return a + b + c
}

func main() {
	bar(foo())
}

/*
== Expected compiler output ==
File "./tests/bad/call/comp_mismatch_number_func.go", line 12, characters 1-4:
error: incorrect number of arguments in call to bar: 2 arguments but 3 parameters
*/
