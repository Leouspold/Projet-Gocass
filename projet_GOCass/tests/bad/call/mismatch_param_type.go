package main

func foo(a int) int {
	return a
}

func main() {
	foo("Hello")
}

/*
== Expected compiler output ==
File "./tests/bad/call/mismatch_param_type.go", line 8, characters 1-4:
error: cannot use type string as type int in argument to foo
*/
