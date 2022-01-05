package main

func main() {
	12++
}

/*
== Expected compiler output ==
File "./tests/bad/unop/incdec_non_lvalue.go", line 4, characters 1-3:
error: cannot assign to a non-left value
*/
