# Proof Theory of Partially Normal Skew Monoidal Categories

## Tarmo Uustalu, Niccolò Veltri and Noam Zeilberger

The skew monoidal categories of Szlachányi are a weakening of monoidal categories where the three
structural laws of left and right unitality and associativity are not required to be isomorphisms but
merely transformations in a particular direction. In previous work, we showed that the free skew
monoidal category on a set of generating objects can be concretely presented as a sequent calculus.
This calculus enjoys cut elimination and admits focusing, i.e. a subsystem of canonical derivations,
which solves the coherence problem for skew monoidal categories.

Here we develop sequent calculi for partially normal skew monoidal categories, which
are skew monoidal categories in which one or more structural laws are invertible. Each normality
condition leads to additional inference rules and equations on them. We prove cut elimination and
we show that the calculi admit focusing. The result is a family of sequent calculi between those of
skew monoidal categories and (fully normal) monoidal categories. On the level of derivability, these
define 8 weakenings of the I,⊗ fragment of intuitionistic non-commutative linear logic.

Structure of the code:
- [src/left-normal](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/left-normal/): Sequent calculus for left-normal skew monoidal categories (Section 3.1 of the paper). The main file is [Everything.agda](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/left-normal/Everything.agda), which takes <1 minute to type-check.
- [src/right-normal](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/right-normal/): Sequent calculus for right-normal skew monoidal categories (Section 3.2 of the paper). The main file is [Everything.agda](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/right-normal/Everything.agda), which takes ~16 minute to type-check.
- [src/assoc-normal](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/assoc-normal/): Sequent calculus for associative-normal skew monoidal categories (Section 3.3 of the paper). The main file is [Everything.agda](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/assoc-normal/Everything.agda), which takes ~50 minute to type-check. Most of the time is spent on termination checking of the proof of associativity of cut rules in [MulticatLaws2.agda](https://github.com/niccoloveltri/skewmoncats-normal/blob/master/src/assoc-normal/MulticatLaws2.agda). Probably adding a TERMINATING pragma would help speed things up.

The formalization uses Agda 2.6.0.
