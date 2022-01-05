package main

func main() {
	2.x = 10
}

/*
== Expected compiler output ==
File "./tests/bad/dot/non_identifier.go", line 4, characters 3-4:
error: use of dot syntax on a non-identifier
*/
