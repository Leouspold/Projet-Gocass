package main

func main() {
	if 42 {

	}
}

/*
== Expected compiler output ==
File "./tests/bad/cond/if_not_bool_cond.go", line 4, characters 4-6:
error: cannot use non-bool type int as if condition
*/
