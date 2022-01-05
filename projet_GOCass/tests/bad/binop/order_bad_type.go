package main

func main() {
	12 > "Hello"
}

/*
== Expected compiler output ==
File "./tests/bad/binop/order_bad_type.go", line 4, characters 12-13:
error: invalid operation: > must be used on int, not on string
*/
