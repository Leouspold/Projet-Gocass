package main

func foo() (int, int, int) {
	return 1, 2, 3
}

func main() {
	var a, b int

	a, b = foo()
}

/*
== Expected compiler output ==
File "./tests/bad/assign/bad_unpack_func.go", line 10, characters 1-13:
error: assignment mismatch: 2 variables but 3 values
*/
