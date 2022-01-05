package main

func main() {
	*nil
}

/*
== Expected compiler output ==
File "./tests/bad/unop/ustar_on_nil.go", line 4, characters 2-5:
error: cannot dereference explicit nil
*/
