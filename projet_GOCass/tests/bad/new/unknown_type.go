package main

func main() {
	var a = new(L)
}

/*
== Expected compiler output ==
File "./tests/bad/new/unknown_type.go", line 4, characters 13-14:
error: cannot allocate an unknown type L
*/
