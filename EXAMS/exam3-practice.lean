import data.set
open set
/-
NOTE: The final exam is comprehensive, but this practice
exam is not. In addition to working through this practice
exam, you should revisit the exam1 and exam2 practice
exams.
-/

/- SETS -/
namespace sets

/-
1.

Prove that 1 is in the set {1, 2, 3, 4, 5}.
-/

example: 1 ∈ ({1, 2, 3, 4, 5}: set ℕ) :=
begin
  _
end

/-
2.

Prove that 1 is not in the set {2, 3, 4}.
-/

example: 1 ∉ ({2, 3, 4}: set ℕ) :=
begin
  _
end

/-
3.

Prove that there does not exist any natural number that is
a member of the empty set of natural numbers.
-/

example: ¬(∃ n:ℕ, n ∈ (∅: set ℕ)) :=
begin
  _
end

/-
4.

Prove that the intersection of the sets of natural numbers
{1, 2} and {3, 4} is empty by showing that for all natural
numbers, they are not in the intersection of {1, 2} and
{3, 4}.
-/

#reduce 2 ∈ ({3, 4}: set ℕ)

example: ∀n: ℕ, n ∉ ({1, 2}: set ℕ) ∩ ({3, 4}: set ℕ) :=
begin
  _
end

/-
5.

Prove that 1 is in the difference between {1, 2, 3} and {3, 4}
-/

example: 1 ∈ ({1, 2, 3}: set ℕ) \ ({3, 4}: set ℕ) :=
begin
  _
end

/-
6.

Prove that {2, 3} is a subset of the union of {1, 2} and {3, 4}
Note: use ⊆ not ⊂
-/

example: ({2, 3}: set ℕ) ⊆ ({1, 2}: set ℕ) ∪ ({3, 4}: set ℕ) :=
begin
  _
end

/-
7.

Prove that {2, 3} is an element of the powerset of {1, 2, 3, 4}
-/

#reduce {2, 3} ∈ 𝒫({1, 2, 3, 4}: set ℕ)
-- ∀ ⦃a : ℕ⦄, a = 3 ∨ a = 2 ∨ false → a = 4 ∨ a = 3 ∨ a = 2 ∨ a = 1 ∨ false

example: {2, 3} ∈ 𝒫({1, 2, 3, 4}: set ℕ) :=
begin
  _
end

end sets

/- RELATIONS -/
namespace relations

/-
The following problems on relations use definitions
of properties of relations from the Lean library that
are identical to those we studied in class.
-/


/-
1.

Prove that disjunction has the symmetric property
-/

example: symmetric or :=
begin
  _
end

/-
2.

Prove that conjunction is a subrelation of disjunction
-/

example: subrelation and or :=
begin
  _
end

/-
3. 

What is the transitive closure of the relation on
ℕ represented by the set { (1,2), (2, 3) }? Write
your answer as a related set in a comment below.
-/

/-
Your answer here: 
-/

end relations

/-
===================================================
Inductive types, functions, properties, and proofs.
====================================================
-/

/-
1.

Define a function, sub_mynat : mynat → mynat → mynat,
that implements subtraction of the second argument, m,
from the first, n. If m >= n, the result should be 0, 
otherwise it should be n - m. Hint: Think about cases
where one of the arguments is zero, and otherwise note
the following pattern: 3 - 2 = 2 - 1 = 1 - 0 = 1.
-/

namespace mynat

inductive mynat : Type 
| zero : mynat
| succ : mynat → mynat

-- def sub_mynat: mynat → mynat → mynat

/-
2.

Prove that ∀ n, sub_mynat n n = 0.
-/


/-
3.

We give you a copy of the add_mynat function
below. Show that our definition of add_mynat 
is associative. 
-/

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

example: ∀(a b c: mynat),
  add_mynat a (add_mynat b c) = add_mynat (add_mynat a b) c :=
begin
  _
end

end mynat


/-
Simple inductive types.
-----------------------
-/

/-
3.

Define a new type called day having
these seven constant constructors: 
sunday, monday, tuesday, wednesday,
thursday, friday, saturday. We will
interpret these constructors as 
representing the actual days of the
week. Write your code below here now.
-/

inductive day : Type
-- finish this definition here


-- We suggest you open the day namespace

open day


/-
4.

Define a function, nextday : day → day,
that, when given a value, d : day, returns 
the day value that represents the next day
of the week. Hint: either write a function
using a "match d with ... end", or, if you
prefer, use a tactic script (to write code!).
If you use a tactic script, use "cases d" 
and for each possible case of d, specify 
the exact day to be returned in that case. 
For extra credit do it both ways and write 
a single sentence to describe how these two 
representations correspond.
-/

def nextday (d : day) : day :=
begin
  _
end


/-
5.

Formalize and prove the proposition that 
for any day, d, if you apply nextday to d
seven times, the result is that very same 
d. Write both the proposition to be proved
and its proof using "example". 
-/

-- Your answer here


/-
Recursive (nested) inductive types.
-----------------------------------
-/

/-
6.

Give an inductive type definition for nat_list,
so that values of this type represent lists of
values of type ℕ.

While there's an infinity of such lists, we can
cleverly define the set inductively with just two
rules.

First, there is an empty list of natural numbers. 
We will represent it with the constant constructor, 
nil_nat. Make it one of the nat_list constructors.

Second, if we are given a nat_list value, l, and 
a ℕ value, e : ℕ, we can always construct a list
that is one longer than by prepending e to l. To
do this, define a constructor called nat_cons. It 
take arguments, e : ℕ and l : ₤st_nat, and yield a 
nat_list.
-/

inductive nat_list : Type 
-- finish the definition here

-- we suggest you open the nat_list namespace

open nat_list


/-
7.

Define X to be the nat_list value that we
interpret as representing the empty list of
natural numbers, []; Y to be the nat_list 
value that represents the list, [1]; and
finally Z to represent the list, [2, 1].
-/

def X : nat_list := _
def Y : nat_list := _
def Z : nat_list := _


/-
8.

Define a function (it will be recursive)
that takes any nat_list value and that
returns its length (a natural number that
indicates how many values are in the list). 
Call the function, length.

The challenge is to see the recursion in 
the definition of the length of a list.
Hint questions: What is the length of the
empty list? What is the length of a list
that is not empty, and that thus must be
of the form (nat_cons h t), where h is the
value at the head of the list and t is the
rest of the list.
-/


/- 
Uncomment the following line
and finish the definition
-/

--def length : nat_list → ℕ 


/-
The stuff that follows is challenging
Get solid on the more basic stuff before 
going here.
-/

/-
9.

Define a function, app (short for "append"), 
that takes two nat_list values, let's call them
l1 and l2, and that returns the nat_list with 
the elements of the first list followed by the
elements of the second list. For example, 
(app Y Z) should return the list [1, 2, 1].


Hint: Consider the possible forms of l1. It 
can only be either nat_nil or (nat_cons h t),
where, once again, h is is first element in 
l1, and t is the rest of the list. Write the 
function recursively accordingly.
-/

def app : nat_list → nat_list → nat_list
_

/-
10.

Prove the following

∀ l1 l2 : nat_list, 
(length l1 + length l2) = length (append l1 l2)

Hint: use proof by induction on l1. There will be
two cases. In the first, l1 will be nat_nil, and
its length will reduce directly to 0. In the second
case, you will show that if the property is true for 
some list l1', it is true for  next bigger list: one 
in the form of (nat_cons h l1').
-/

example : ∀ l1 l2 : nat_list, 
(length l1 + length l2) = 
length (app l1 l2) :=
begin
  _
end

/- Formal Languages -/

namespace formal
/-
1.

Extend the following formal language to incorporate "or"
in a manner similar to "and"
-/

inductive pVar : Type 
| mk : ℕ → pVar

inductive pExp : Type
| mk_lit_pexp : bool → pExp
| mk_var_pexp : pVar → pExp
| mk_not_pexp : pExp → pExp
| mk_and_pexp : pExp → pExp → pExp

open pExp

def pInterp := pVar → bool

def pEval : pExp → pInterp → bool 
-- how to evaluate literal expression
| (mk_lit_pexp b) i := b
-- how to evaluate variable expression
| (mk_var_pexp v) i := i v
-- how to evaluate a "not" expression
| (mk_not_pexp e) i := bnot (pEval e i)
-- how to evaluate an "and" expression
| (mk_and_pexp e1 e2) i := 
    band (pEval e1 i) (pEval e2 i)

end formal
