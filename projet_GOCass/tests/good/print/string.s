	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $S_1, %rdi
	call print_string
	call print_space
	movq %rbp, %rsp
	popq %rbp
	ret

print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_bool:
        test    %rdi, %rdi
        jnz     print_true
        mov     $S_false, %rdi
        call    printf
        xorq    %rax, %rax
        ret
print_true:
        mov     $S_true, %rdi
        call    printf
        xorq    %rax, %rax
        ret
print_string:
        mov     %rdi, %rsi
        mov     $S_string, %rdi
        xorq    %rax, %rax
        call    printf
        ret    
print_space:
        mov     $S_space, %rdi
        xorq    %rax, %rax
        call    printf
        ret   
	.data
S_int:
	.string "%ld"
S_true:
	.string "true"
S_false:
	.string "false"
S_string:
	.string "%s"
S_space:
	.string " "
S_1:
	.string "a"
