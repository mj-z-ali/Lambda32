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

- _p_ :≡ _g_(_r_<sub>i</sub>, ..., _r_<sub>k</sub>, ..., _r_<sub>n</sub>), where _g_ is _n_-ary and each _r_<sub>i</sub> is an R-Register such that _r_<sub>i</sub> ≠ _r_<sub>k</sub>.
- _p_ :≡ _g_(_v_<sub>1</sub>, _v_<sub>2</sub>), where _g_ is a binary operation and each _v_<sub>i</sub> is a Variable in the ISA.
- _p_ :≡ _g_(_v_, _c_), where _g_ is a binary operation.
- _p_ :≡ _g_(_v_, _f_), where _g_ is a binary operation and _f_ is a function (defined later in <a href="#termf">Term</a>).
- _p_ :≡ _g_(_v_, _p_<sub>i</sub>), where _g_ is a binary operation and _p_<sub>i</sub> is an Operative Instruction in the ISA.
- _p_ :≡ -(_v_), where - is a unary operation.
- _p_ :≡ -(_c_), where - is a unary operation.
- _p_ :≡ -(_f_), where - is a unary operation and _f_ is a function (defined later in <a href="#termf">Term</a>).
- _p_ :≡ -(_p_<sub>i</sub>), where - is a unary operation and _p_<sub>i</sub> is an Operative Instruction in the ISA.

#### Definition of a Term <a href="#ref1">[1]</a>

A Term _t_ is such that either:

- _t_ is a Variable, or
- _t_ is a Constant, or
- _t_ is an Operative Instruction, or
- _t_ is an IF THEN ELSE Instruction (<a href="#if">defined later</a>), or
- _t_ :≡ _f_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), where _f_ is an _n_-ary function and each _t_<sub>i</sub> is a Term <a id="#termf"></a>

#### Definition of a Formula <a href="#ref1">[1]</a>

A Formula φ is such that either:

- φ :≡ = (_t_<sub>1</sub>, _t_<sub>2</sub>), where _t_<sub>1</sub> and _t_<sub>2</sub> are Terms of the ISA.
- φ :≡ _P_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), where _P_ is an _n_-ary predicate and each _t_<sub>i</sub> is a Term.
- φ :≡ ¬(α), where α is a Formula of the ISA.
- φ :≡ \\/(α, β) where α and β are formulas of the ISA.
- φ :≡ /\\(α, β) where α and β are formulas of the ISA.

#### Definition of an IF THEN ELSE Instruction <a id="#if"></a>

If φ is a Formula in the ISA and _t_<sub>1</sub> and _t_<sub>2</sub> are Terms, then an IF THEN ELSE Instruction is defined as follows:

IF φ THEN _t_<sub>1</sub> ELSE _t_<sub>2</sub>

#### Definition of the ISA Structure <a href="#ref1">[1]</a>

The ISA Structure _M_ is the set _A_ { i | -2<sup>31</sup> ≤ i ≤ 2<sup>31</sup> - 1}, called the universe of _M_, together with:

- For each Constant c, an element c<sup>_M_</sup> of _A_.
- For each _n_-ary function _f_, a function _f_<sup>_M_</sup> : _A_<sup>n</sup> -> _A_.
- For each _n_-ary Operative Instruction _g_, an Operative Instruction _g_<sup>_M_</sup> : _A_<sup>n</sup> -> _A_.

#### Definition of the Variable Assignment Function <a href="#ref1">[1]</a>

If _M_ is the ISA Structure, then a Variable Assignment Function _s_ maps each Variable in the ISA to an element of the universe _A_. In other words, _s_ is a function with domain Variable and codomain _A_ as follows:

Variable -> _A_

#### Definition of the Term Assignment Function <a href="#ref1">[1]</a>

For the ISA Structure _M_ and the Variable Assignment Function _s_ into _M_, the Term Assignment Function _s_' has a domain Term of the ISA and codomain _A_ and is defined recursively as follows:

- If _t_ is a Variable, _s_'(_t_) = _s_(_t_)
- If _t_ is a Constant c, _s_'(_t_) = c<sup>_M_</sup>
- If _t_ :≡ _g_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), such that _g_ is an _n_-ary Operative Instruction in the ISA, then _s_'(_t_) = _g_<sup>_M_</sup>(_s_'(_t_<sub>i</sub>), ..., _s_'(_t_<sub>k</sub>), ..., _s_'(_t_<sub>n</sub>))
- If _t_ :≡ _f_(_t_<sub>i</sub>, ..., _t_<sub>k</sub>, ..., _t_<sub>n</sub>), such that _f_ is an _n_-ary function in the ISA, then _s_'(_t_) = _f_<sup>_M_</sup>(_s_'(_t_<sub>i</sub>), ..., _s_'(_t_<sub>k</sub>), ..., _s_'(_t_<sub>n</sub>))

#### Definition of the Assignment Instruction

The Assignment Instruction, defined as:

_v_ -> _t_, where _v_ is a Variable and _t_ is a Term in the ISA,

assigns a Variable _v_ to a mapped element of _A_ from a Term _t_ after implicity doing the following:

_v_ -> _s_'(_t_), where _v_ is a Variable of the ISA and _s_' is a Term Assignment Function.

#### References

<a id="ref1">[1]</a> <a href="https://knightscholar.geneseo.edu/geneseo-authors/6?utm_source=knightscholar.geneseo.edu%2Fgeneseo-authors%2F6&utm_medium=PDF&utm_campaign=PDFCoverPages"> Leary, Christopher C. and Kristiansen, Lars, "A Friendly Introduction to Mathematical Logic" (2015). Geneseo Authors. 6. </a>
