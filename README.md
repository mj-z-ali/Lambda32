# Lambda32

## Definitions

### Definition of an R-register

The ISA contains thirty-two 32-bit general purpose R-registers defined as follows: R0, ..., R31

### Definition of a Variable

If R is an R-register in the ISA, then a variable is either:

- An R-register R, or
- A memory location defined as:
  - R<sub>i</sub>[R<sub>j</sub>], where R<sub>i</sub> and R<sub>j</sub> are each R-registers and R<sub>i</sub> holds the base memory address and R<sub>j</sub> the index.
  - [R], where R holds the memory address.

### Definition of a Constant

A constant is a 32-bit sized integer in the range of [-2<sup>31</sup>, 2<sup>31</sup> - 1].

### Definition of a Term

A Term t is such that either:

- t is a Variable, or
- t is a Constant, or
- t is f(t<sub>1</sub>, t<sub>2</sub>, ..., t<sub>n</sub>) where f is an n-ary function and each t<sub>i</sub> is a Term.

### Definition of Assignment Function.
