package main

func main() {
	for i := 1; 42; i++ {
		fmt.Print(i)
	}
}

/*
== Expected compiler output ==
File "./tests/bad/cond/for_not_bool_cond.go", line 4, characters 13-15:
error: cannot use non-bool type int as for condition
*/
