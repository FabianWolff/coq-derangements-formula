# Derangements Formula in Coq

A derangement is a permutation of elements of a set where no element is mapped to itself (i.e. the permutation has no fixed points).

The number of derangements of a set of size $n$ is equal to $!n = \lfloor \frac{n!}{e} \rceil$ (where $\lfloor\cdot\rceil$ means rounding) and is hence also known as the subfactorial of $n$.


The files in this repository formalize the proof of the above formula in Coq. Verify them in this order:

```
coqc drmcorrect.v
coqc drmnodup.v
coqc drmcomplete.v
coqc drmformula.v
```

The proof is based on a function `drm_construct`, which constructs all derangements of size $n$ as a list of maps on natural numbers. This function/its result is then proved correct (it produces only derangements), complete (it produces all derangements), and duplicate-free, and finally, the actual formula is proved in `drmformula.v`.
