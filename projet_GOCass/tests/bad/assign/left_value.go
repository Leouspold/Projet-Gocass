package main

func main() {
	1 = 2
}

/*
== Expected compiler output ==
File "./tests/bad/assign/left_value.go", line 4, characters 1-6:
error: cannot assign to a non-left value
*/
