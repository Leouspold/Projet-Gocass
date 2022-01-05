package main

func main() {
	12 && "Hello"
}

/*
== Expected compiler output ==
File "./tests/bad/binop/logic_bad_type.go", line 4, characters 1-3:
error: invalid operation: && must be used on bool, not on int
*/
