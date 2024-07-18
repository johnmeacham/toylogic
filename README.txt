RPN like theorem prover

---- stack operations ----
0 duplicate top of lemma stack
1-9 move the specified formula to the top of the stack
shift A-Z copy the specified formula from the theorem list to the top of the stack
- delete top of lemma stack
p promote the top of the lemma stack to a theorem
---- rules of inference ----
d (degeneralize) replace a quantifier with an unbound term
g (generalize) universally quantify all unbound terms
m use modus pones to apply the top of the stack to the second item in the stack
---- utilities ----
h show this help
u undo last operation
ESC quit
-----
