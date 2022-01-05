package main

func main() {
	nil.x = 10
}

/*
== Expected compiler output ==
File "./tests/bad/dot/nul_struct.go", line 4, characters 5-6:
error: use of untyped nil
*/
