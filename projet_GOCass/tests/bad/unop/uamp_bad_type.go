package main

func main() {
	&"Hello"
}

/*
== Expected compiler output ==
File "./tests/bad/unop/uamp_bad_type.go", line 4, characters 8-9:
error: cannot take the address of non-left value
*/
