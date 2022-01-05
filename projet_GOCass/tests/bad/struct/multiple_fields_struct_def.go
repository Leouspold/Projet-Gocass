package main

type A struct {
	x int
	x int
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/struct/multiple_fields_struct_def.go", line 5, characters 1-2:
error: duplicate field x in structure A
*/
