package main

type A struct {
	x int
}

type A struct {
	x int
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/struct/multiple_struct_def.go", line 7, characters 5-6:
error: structure A redeclared
*/
