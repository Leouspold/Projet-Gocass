package main

func main() {
    var x = nil
}

/*
== Expected compiler output ==
File "./tests/bad/vars/nil.go", line 4, characters 4-15:
error: cannot infer type of variable assignation from nil pointer
*/
