package main

func main() int {
	return 42
}

/*
== Expected compiler output ==
File "./tests/bad/main/return_value_main.go", line 3, characters 5-9:
error: func main must have no parameters and no return values
*/
