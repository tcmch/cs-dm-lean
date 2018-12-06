/-

This exam focuses on assessing your 
ability to write and prove propositions 
in predicate logic, with an emphasis on
predicates, disjunctions, and existentially 
quantified propositions. There are three 
parts: 

A: Predicates [20 points in 4 parts]
B: Disjuctions [40 points in 2 parts]
C. Existentials [40 point in 2 parts]
-/


/- ******************************** -/
/- *** A. PREDICATES [20 points] ***-/
/- ******************************** -/

/-
1a. Define a function called isOdd that
takes an argument, n : ℕ, and returns a 
proposition that asserts that n is odd.
The function will thus be a predicate on 
values of type ℕ. Hint: a number is odd
if it's one more than an even number.
-/



/-
1b. To test your predicate, use "example"
to write and prove isOdd(15).
-/



/-
1c. Define isSmall : ℕ → Prop, to be a
predicate that is true exactly when the
argument, n, is such that n = 0 ∨ n = 1
∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5. (Don't
try to rewrite this proposition as an 
inequality; just use it as is.) 
-/



/-
1d. Define a predicate, isBoth(n:ℕ) that 
is true exacly when n satisfies both the
isOdd and isSmall predicates. Use isOdd 
and isSmall in your answer.
-/




/- ******************* -/
/- *** DISJUNCTIONS ***-/
/- ******************* -/

/-
2. [20 Points]

Jane walks to school or she carries 
her lunch. In either case, she uses
a bag. If she walks, she uses a bag for
her books. If she carries her lunch, she
uses a bag to carry her food. So if she
walks, she uses a bag, and if she carries
her lunch, she uses a bag. From the fact
that she walks or carries her lunch, and
from the added facts that in either case 
she uses a bag, we can conclude that she 
uses a bag.

Using Walks, Carries, and Bag as names
of propositions, write a Lean example 
that asserts the following proposition; 
then prove it. 

If Walks, Carries, and Bag are 
propositions, then if (Walks ∨ Carries) 
is true, and then if (Walks implies Bag)
is true, and then if (Carries implies Bag)
is true, then Bag is true.

Here's a start.

example : ∀ (Walks Carries Bag : Prop), ...
-/




/-
3. [20 Points]

Prove the following proposition.
-/

example : 
    ∀ (P Q R : Prop), 
    (P ∧ Q) → (Q ∨ R) → (P ∨ R) :=
begin
_
end


/- *********************** -/
/- *** C. EXISTENTIALS  ***-/
/- *********************** -/

/-
4. [20 points]

Referring to the isBoth predicate you
defined in question #1, state and prove 
the proposition that there *exists* a 
number, n, that satisfies isBoth. Remember 
that you can use the unfold tactic to 
expand the name of a predicate in a goal.
Use "example" to state the proposition.
-/




/-
5. [20 points]

Suppose that Heavy and Round are
predicates on values of any type, T.
Prove the proposition that if every 
t : T is Heavy (satisfies the Heavy 
predicate) and if there exists some 
t : T that is Round (satisfies the
Round predicate) then there exists 
some t : T is both Heavy and Round
(satisfies the conjunction of the
two properties). 
-/

example : 
∀ T : Type, ∀ (Heavy Round : T → Prop),
(∀ t, Heavy t) → (∃ t, Round t) →
(∃ t, Heavy t ∧ Round t) :=
begin
_
end


