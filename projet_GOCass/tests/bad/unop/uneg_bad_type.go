package main

func main() {
	-"Hello"
}

/*
== Expected compiler output ==
File "./tests/bad/unop/uneg_bad_type.go", line 4, characters 8-9:
error: invalid operation: - must be used on int, not on string
*/
