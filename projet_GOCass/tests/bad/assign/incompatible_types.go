package main

func main() {
	var a int

	a = "Hello world"
}

/*
== Expected compiler output ==
File "./tests/bad/assign/incompatible_types.go", line 6, characters 1-18:
error: cannot use type string as type int in assignment
*/
