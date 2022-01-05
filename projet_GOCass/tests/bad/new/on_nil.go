package main

func main() {
	var a = new(nil)
}

/*
== Expected compiler output ==
File "./tests/bad/new/on_nil.go", line 4, characters 9-17:
error: cannot allocate on nil
*/
