package main

func main() {
	var a, b int = 1, 2, 3
}

/*
== Expected compiler output ==
File "./tests/bad/vars/bad_unpack.go", line 4, characters 1-23:
error: assignment mismatch: 2 variables but 3 values
*/
