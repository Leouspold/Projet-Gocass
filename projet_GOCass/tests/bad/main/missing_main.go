package main

func f() int {
	return 42
}

/*
== Expected compiler output ==
File "./tests/bad/main/missing_main.go":
error: missing method main
*/
