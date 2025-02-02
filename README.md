[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-24ddc0f5d75046c5622901739e7c5dd533143b0c8e959d652212380cedb1ea36.svg)](https://classroom.github.com/a/y
cm7-Tkm)

## Notes
- Using "_main" and "_conclusion" doesn't work for MacOSX therefore the function using it: `correct-label` was removed from the prelude and conclusion functions.
- The code was tested on a Mac OSX M1 machine.

## Homework instructions

For your homework exercises, you will be expected to implement various
compiler passes. It will ultimately be up to you how exactly to do
this, but for the first assignment you are given code templates in
`compiler.rkt` to fill out.

Before each assignment (and when told to by the instructor), you may need to update
this code by pulling updates from GitHub by running this command from inside the folder:

```
   git pull
```

As you fill out the functions in `compiler.rkt`, tests are run with the
`run-tests.rkt` module. You can run these tests either from the command
line with:

```
   racket run-tests.rkt
```

Or by opening and running `run-tests.rkt` in DrRacket.

Before running the compiler tests, you need to compile
`runtime.c` (see below).

## Public student code

Utility code, test suites, etc. for the compiler course.

This code will be described in the Appendix of the book.

The `runtime.c` file needs to be compiled and linked with the assembly
code that your compiler produces. To compile `runtime.c`, do the
following
```
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named `runtime.o`. The -g flag is to tell the
compiler to produce debug information that you may need to use
the gdb (or lldb) debugger.

On a Mac with an M1 (ARM) processor, use the `-arch x86_64` flag to
compile the runtime:
```
   gcc -c -g -std=c99 -arch x86_64 runtime.c
```


Next, suppose your compiler has translated the Racket program in file
`foo.rkt` into the x86 assembly program in file `foo.s` (The .s filename
extension is the standard one for assembly programs.) To produce
an executable program, you can then do
```
  gcc -g runtime.o foo.s
```
which will produce the executable program named a.out.

There is an example "compiler" in the file `compiler.rkt`.  That
file defines two passes that translate R_0 programs to R_0 programs
and tests them using the `interp-tests` function from `utilities.rkt`. It
tests the passes on the three example programs in the tests
subdirectory. You may find it amusing (I did!) to insert bugs in the
compiler and see the errors reported. Note that `interp-tests` does not
test the final output assembly code; you need to use `compiler-tests`
for that purpose. The usage of `compiler-tests` is quite similar to
`interp-tests`. Example uses of these testing procedures appear in
`run-tests.rkt`.

As new languages are added, `run-tests.rkt` will be extended to
test new passes. You will be provided with new iterations of
the script for each assignment.
