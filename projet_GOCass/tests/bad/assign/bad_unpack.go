package main

func main() {
	var a, b int

	a, b = 1, 2, 3
}

/*
== Expected compiler output ==
File "./tests/bad/assign/bad_unpack.go", line 6, characters 1-15:
error: assignment mismatch: 2 variables but 3 values
*/
