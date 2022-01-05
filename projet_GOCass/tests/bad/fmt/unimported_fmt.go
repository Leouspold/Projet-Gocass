package main

func main() {
	fmt.Print("Hello World")
}

/*
== Expected compiler output ==
File "./tests/bad/fmt/unimported_fmt.go":
error: fmt used but not imported
*/
