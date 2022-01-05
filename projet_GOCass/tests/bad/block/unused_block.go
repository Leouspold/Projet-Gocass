package main

func main() {
	if true {
		var a int
	}
}

/*
== Expected compiler output ==
File "./tests/bad/block/unused_block.go", line 5, characters 6-7:
error: a declared but not used
*/
