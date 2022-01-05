package main

func main() {
	var a int = "Hello world"
}

/*
== Expected compiler output ==
File "./tests/bad/vars/incompatible_types.go", line 4, characters 1-26:
error: cannot use type string as type int in assignment
*/
