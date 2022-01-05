package main

type A struct {
	x int
}

func main() {
	var a A

	a.y = 10
}

/*
== Expected compiler output ==
File "./tests/bad/dot/unknown_field_struct.go", line 10, characters 3-4:
error: type A has no field y
*/
