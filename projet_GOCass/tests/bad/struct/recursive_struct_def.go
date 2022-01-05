package main

type A struct {
	a A
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/struct/recursive_struct_def.go", line 3, characters 5-6:
error: recursive field a in the struct A
*/
