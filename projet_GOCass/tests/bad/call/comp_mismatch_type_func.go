package main

func foo() (int, string) {
	return 12, "Hello"
}

func bar(a int, b int) int {
	return a + b
}

func main() {
	bar(foo())
}

/*
== Expected compiler output ==
File "./tests/bad/call/comp_mismatch_type_func.go", line 12, characters 1-4:
error: cannot use type string as type int in argument to bar
*/
