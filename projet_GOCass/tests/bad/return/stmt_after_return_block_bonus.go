package main

func foo() int {
	{
		return 42
	}

	return 42
}

func main() {}

/*
== Expected compiler output ==
File "./tests/bad/return/stmt_after_return_block.go", line 3, characters 15-48:
error: block contains unreachable code
*/
