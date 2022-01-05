package main

func main() {
	foo()
}

/*
== Expected compiler output ==
File "./tests/bad/call/unknown_func.go", line 4, characters 1-4:
error: call to unknown function foo
*/
