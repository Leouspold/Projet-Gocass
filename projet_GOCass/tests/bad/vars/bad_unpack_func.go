package main

func foo() (int, int, int) {
	return 1, 2, 3
}

func main() {
	var a, b = foo()
}

/*
== Expected compiler output ==
File "./tests/bad/vars/bad_unpack_func.go", line 8, characters 1-17:
error: assignment mismatch: 2 variables but 3 values
*/
