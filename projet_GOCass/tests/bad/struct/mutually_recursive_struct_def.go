package main

type A struct {
	b B
}

type B struct {
	a A
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/struct/mutually_recursive_struct_def.go", line 3, characters 5-6:
error: recursive field b in the struct A
*/
