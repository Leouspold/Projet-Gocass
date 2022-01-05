package main

func main() {
	"Hello"++
}

/*
== Expected compiler output ==
File "./tests/bad/unop/incdec_bad_type.go", line 4, characters 7-8:
error: invalid operation: ++ must be used on int, not on string
*/
