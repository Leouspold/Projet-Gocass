package main

func main() {
	*12
}

/*
== Expected compiler output ==
File "./tests/bad/unop/ustar_on_nonptr.go", line 4, characters 2-4:
error: cannot dereference non-pointer int
*/
