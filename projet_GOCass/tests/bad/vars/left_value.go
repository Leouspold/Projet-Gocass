package main

func foo(x int) int {
	return x
}

func main() {
	x := 1

	foo(x) = 2
}

/*
== Expected compiler output ==
File "./tests/bad/vars/left_value.go", line 10, characters 1-11:
error: cannot assign to a non-left value
*/
