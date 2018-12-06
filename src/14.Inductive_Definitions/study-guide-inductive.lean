/-
===================================================
Inductive types, functions, properties, and proofs.
====================================================
-/

/-
Simple inductive types.
-----------------------
-/

/-
1.

Define a new type called day having
these seven constant constructors: 
sunday, monday, tuesday, wednesday,
thursday, friday, saturday. We will
interpret these constructors as 
representing the actual days of the
week. Write your code below here now.
-/

inductive day : Type
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

-- We suggest you open the day namespace

open day


/-
2.

Define a function, nextday : day → day,
that, when given a value, d : day, returns 
the day value that represents the next day
of the week. Hint: either write a function
using a match d with ... end, or, if you
can use a tactic script (to write code!).
Use cases d and for each possible case of
d, specify the exact day to be returned in
that case. For extra credit do it both ways
and write a single sentence to describe how
these two representations correspond.
-/

def nextday (d : day) : day :=
begin
cases d,
exact monday,
exact tuesday,
exact wednesday,
exact thursday,
exact friday,
exact saturday,
exact sunday,
end


def nextday' (d : day) :=
match d with
| sunday := monday
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := saturday
| saturday := sunday
end

/-
3.

Formalize and prove the proposition that 
for any day, d, if you apply nextday to d
then nextday to the result, seven times, 
the result is that very same d. 
-/

example : ∀ d : day, 
nextday ( nextday ( nextday (nextday (nextday (nextday (nextday d)))))) = d :=
begin
assume d,
cases d,
repeat { apply rfl }, -- don't write it 7 times!
end



/-
Recursive (nested) inductive types.
-----------------------------------
-/

/-
4.

Give an inductive type definition for nat_list,
so that values of this type represent lists of
values of type ℕ.

While there's an infinity of such lists, we can
cleverly define the set inductively with just two
rules.

First, there is an empty list of natural numbers. We will represent it with the constant constructor, 
nil_nat. Make it one of the nat_list constructors.

Second, if we are given a nat_list value, l, and 
a ℕ value, e : ℕ, we can always construct a list
that is one longer than by prepending e to l. To
do this, define a constructor called nat_cons. It take arguments, e : ℕ and l : ₤st_nat, and yield a 
nat_list.
-/

inductive nat_list : Type 
| nat_nil : nat_list
| nat_cons : ℕ → nat_list → nat_list 

-- we suggest you open the nat_list namespace

open nat_list


/-
5.

Define X to be the nat_list value that we
interpret as representing the empty list of
natural numbers, []; Y to be the nat_list 
value that represents the list, [1]; and
finally Z to represent the list, [2, 1].
-/

def X := nat_nil
def Y := (nat_cons 1 nat_nil)
def Z := (nat_cons 2 Y)


/-
6.

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


def length : nat_list → ℕ 
| nat_nil := 0
| (nat_cons h t) := 1 + length t


/-
The stuff that follows is challenging
Get solid on the basic stuff before 
going here.
-/

/-
7.

Define a function, app, that take two
nat_list values as arguments and that then
returns the nat_list that is the first one
followed by the second one. Let's call the
arguments l1 and l2.

Consider the possible forms of l1. It can
only be either nat_nil or (nat_cons h t),
where, once again, h would be the first
element in l1, and t would be the rest of
the list. Write the function recursively
accordingly.
-/

def app : nat_list → nat_list → nat_list
| nat_nil l2 := l2
| (nat_cons h t) l2 := nat_cons h (app t l2)


/-
8.

Prove the following

∀ l1 l2 : nat_list, 
    (length l1 + length l2) = length (append l1 l2)

Hint: use proof by induction on l1. There will be
two cases. In the first, l1 will be nat_nil, and
its length will reduce directly to 0. In the second
case, you will show that the property is true for a
next bigger list: one in the form of (nat_cons h t).
-/

example : ∀ l1 l2 : nat_list, 
            (length l1 + length l2) = 
            length (app l1 l2) :=
begin
intros l1 l2,
induction l1 with l1' n h,
-- base case
-- simplify using rules in app and length defs
simp [app],
simp [length],

-- inductive case
-- simplify using app and length rules in one line
simp [app,length],

-- now use induction hypothesis to rewrite goal
rw <-h,

-- and the rest is simple arithmetic manipulation
simp,
--rw 
end