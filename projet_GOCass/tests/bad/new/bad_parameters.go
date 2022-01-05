package main

func main() {
	var a = new(int, string)
}

/*
== Expected compiler output ==
File "./tests/bad/new/bad_parameters.go", line 4, characters 9-25:
error: new expects exactly one type
*/
