package main

func main() {
	var a int

	a.x = 10
}

/*
== Expected compiler output ==
File "./tests/bad/dot/on_non_struct.go", line 6, characters 3-4:
error: type int is not a structure
*/
