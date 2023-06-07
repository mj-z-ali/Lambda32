# Lambda32

### ISA

#### Definition of an R-Register

The ISA contains thirty-two 32-bit general purpose R-Registers defined as follows:

R0, ..., R31

#### Definition of a Variable

If _r_ is an R-Register in the ISA, then a variable is either:

- An R-Register _r_, or
- A memory location defined as:
  - _r_<sub>i</sub>[_r_<sub>j</sub>], where _r_<sub>i</sub> and _r_<sub>j</sub> are each R-Registers and _r_<sub>i</sub> holds the base memory address and _r_<sub>j</sub> the index.
  - [_r_], where _r_ holds the memory address.

#### Definition of a Constant

A constant is a 32-bit sized integer in the range [-2<sup>31</sup>, 2<sup>31</sup> - 1].

#### Definition of an Operative Instruction

For a Variable _v_ in the ISA; a Constant _c_; an R-Register _r_; and _g_ representing either the add operation + or the multiplication \*, an Operative Instruction _p_ is such that either:

- _p_ :≡ _g_(_r_<sub>i</sub>, ..., _r_<sub>k</sub>, ..., _r_<sub>n</sub>), where _g_ is n-ary and each _r_<sub>i</sub> is an R-Register such that _r_<sub>i</sub> ≠ _r_<sub>k</sub>.
- _p_ :≡ _g_(_v_<sub>1</sub>, _v_<sub>2</sub>), where _g_ is binary and each _v_<sub>i</sub> is a Variable in the ISA.
- _p_ :≡ _g_(_v_, _c_), where _g_ is binary.
- _p_ :≡ _g_(_v_, _f_), where _g_ is binary and _f_ is a function (defined later in Term).
- _p_ :≡ _g_(_v_, _p_<sub>i</sub>), where _g_ is binary and _p_<sub>i</sub> is an Operative Instruction in the ISA.

#### Definition of a Term

A Term _t_ is such that either:

- _t_ is a Variable, or
- _t_ is a Constant, or
- _t_ is an Operative Instruction, or
- _t_ :≡ _f_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), where _f_ is an n-ary function and each _t_<sub>i</sub> is a Term.

#### Definition of a Formula

A Formula φ is such that either:

- φ :≡ = (_t_<sub>1</sub>, _t_<sub>2</sub>), where _t_<sub>1</sub> are _t_<sub>2</sub> Terms of the ISA.
- φ :≡ _P_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), where _P_ is an n-ary predicate and each _t_<sub>i</sub> is a Term.
- φ :≡ ¬(α), where α is a Formula of the ISA.
- φ :≡ \\\/(α, β) where α and β are formulas of the ISA.
- φ :≡ /\\(α, β) where α and β are formulas of the ISA.

#### Definition of a Term Assignment Instruction.

If _t_ is a Term in the ISA, a Term Assignment Instruction
