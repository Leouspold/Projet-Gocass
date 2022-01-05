package main

func foo() (int, string) {
	return 1, "Hello"
}

func main() {
	var a, b int

	a, b = foo()
}

/*
== Expected compiler output ==
File "./tests/bad/assign/incompatible_types_func.go", line 10, characters 1-13:
error: cannot use type string as type int in assignment
*/
