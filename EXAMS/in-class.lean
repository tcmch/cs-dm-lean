/-
This problem tests your ability to 
contruct proofs using case analysis 
on a disjunction, ∀ elimination, and 
or introduction. 

Remember, To eliminate a ∀ in a goal, 
of the form, ∀ x, P x, introduce an
arbitrary value x into your context
(using intro or assume) and then show
P x for that x. (Of course you will 
pick a sensible name instead of x for
the value being introduced into the
context.) The idea is that by showing 
P x for an arbitrarily assumed value,
x, you thereby show P x for any x, and 
thus you show P x for ∀ x. 
-/

example : 
    ∀ (x : Type), 
    ∀ (p q : x → Prop), 
    (∀ x, p x) ∨ (∀ x, q x) → 
    ∀ x, p x ∨ q x :=
_

