package main

func main() {
	!"Hello"
}

/*
== Expected compiler output ==
File "./tests/bad/unop/unot_bad_type.go", line 4, characters 8-9:
error: invalid operation: ! must be used on bool, not on string
*/
