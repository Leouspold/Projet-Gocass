package main

func foo() (int, string) {
	return 1, "Hello"
}

func main() {
	var a, b int = foo()
}

/*
== Expected compiler output ==
File "./tests/bad/vars/incompatible_types_func.go", line 8, characters 1-21:
error: cannot use type string as type int in assignment
*/
