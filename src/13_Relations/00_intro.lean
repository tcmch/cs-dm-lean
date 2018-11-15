namespace relation_2102_ns
section relation_2102_sec

/-
Let β be an arbitrary type, and r be
a binary relation on elements of type,
β. 
-/
variable {β : Type} 
variable (r : β → β → Prop)

/-
Applying r to two values, x and y, of
type, β, yields a proposition. You can
thus think of r as a property of pairs 
of values. If the proposition is true,
then the ordered pair, (x, y), is in 
the relation, otherwise it's not.
-/
variables x y : β  
#check r x y 

/-
In the preceding example, we wrote 
the relation name before the arguments.
It's often more natural to write in in
between the arguments. We call such a
notation an infix notation. Lean gives
us a way to extend the syntax of Lean
by adding infix operators to reduce to
known prefix operators. Here we define
two infix versions of r, one called R,
and one called ≺. The number, 50, in the
following lines defines the precedence
of this operator, i.e., how tightly it
binds when appearing in an expression
with other operators.
-/

local infix `R`:50 := r
local infix `≺`:50 := r

/-
Now we can use either x R y or x ≺ y
to mean the same thing as r x y. We'll
use the x R y style in the file. Lean's
libraries happen to use x ≺ y, but they
mean the same thing, as we just said.
-/
#check x R y 
#check x ≺ y


-- EXAMPLE: THE EQUALITY RELATION

/-
Let's look at equality as a binary
relation. The first thing to know is
that an expression, such as 1 = 1, is
a convenient way of writing "eq 1 1".
The = notation is defined as an infix
version of eq in just the same way 
that we defined R and ≺ to be infix
versions of r. Check to see that the
following expressions mean the same
thing.
-/
#reduce 1 = 1
#reduce eq 1 1

/-
Let's look at the actual definition
of eq in Lean's libraries. 
-/
#print eq
/-
Just look at the first line, skipping 
the constructor for now. What is says
is that for any Type, α, eq is a binary
relation on values of that type. The "Pi" 
symbol, Π,  is like ∀. ∀ is used when 
working with propositions, but equality 
is defined for any type, so we use Π 
instead. You should read the definition as
saying that if you give eq any type, you 
get back a binary relation on values of 
that type: namely one for which the only 
proofs that can be constructed are given
by eq.refl, which takes just one argument,
α, and returns a proof of α = α.

We thus expect the type of "eq ℕ" to be 
a binary relation on ℕ values. We preface eq in the following examples with @, which
tells Lean not to use implicit typing for the type argument, α, to eq. We really do have to give a type argument explicitly.
-/

#check @eq nat 
#check @eq β 

/-
We now see that for any type, α, such as 
ℕ, or, in this file, β, eq α is a binary relation on the set of values of type, α. It is thus of type, α → α → Prop. That is
the signal that you're looking at a binary
relation in Lean.
-/

-- REFLEXIVE

/-
Given that we now see that eq β is a binary relation, let's assert and prove
that it is a reflexive relation.

EXERCISE: Think about and discuss 
what it means for equality to be a
reflexive relation. Do you believe
it is reflexive?
-/

lemma eq_refl : reflexive (@eq β) :=
begin
unfold reflexive,
intro, apply rfl,
end


-- SYMMETRIC

/-
A relation is symmetric if, whenever
two values, and and y, are related, 
y and x are related, in the opposite
order.
-/
def symmetric := ∀ ⦃x y⦄, x R y → y R x


/-
Let's prove that equality is symmetric.
Of course we're cheating a little here
by using a rule already in the libraries
that eq is symmetric: the rule, eq.symm. 
-/
lemma eq_symm : symmetric (@eq β) :=
begin
unfold symmetric,
intros, 
apply eq.symm, 
assumption,
end

/-
EXERCISE: Is the real-world "likes" 
relation, as in "has-a-crush-on", a  symmetric relation? How about Facebook's 
"likes" relation?
-/

-- TRANSITIVE

/-
A binary relation on values of some 
type, β, is said to be transitive if
whenever x and y are related, and y 
and z are related, then x and z are
related. 
-/
def transitive := 
    ∀ ⦃x y z⦄, x R y → y R z → x R z

/-
EXERCISE: Is equality transitive?
-/

lemma eq_trans : transitive (@eq β) :=
begin
unfold transitive,
intros x y z xy yz,
apply eq.trans xy yz,
end

/-
An equivalence relation is a binary
relation that is reflexive, symmetric,
and transitive.
-/
def equivalence := reflexive r ∧ symmetric r ∧ transitive r

/-
Is eq an equivalence relation? Sure.
-/

theorem eq_equiv : equivalence (@eq β) :=
begin
unfold equivalence,
split, exact eq_refl,
split, exact eq_symm, exact eq_trans
end

/-
Let's discuss another equivalence 
relation. Consider the set ℕ / 12,
the natural numbers modulo 12. 

What is 2 mod 12? What is 14 mod 12?
What is 26 mod 12. All these numbers,
and indeed any natural number of the
form, 2 + k * 12 are congruent to 2
mod 12. 
-/

#reduce 2 % 12
#reduce 14 % 12
#reduce 26 % 12

/-
This entire set of numbers mod 12 
forms an equivalence class. Let's
formalize and prove this proposition.
-/


/-
First, the relation itself.
-/
def mod_12_equiv : ℕ → ℕ → Prop :=
    λ x y, x % 12 = y % 12

/-
Now a simple test case as a sanity
check.
-/
example : mod_12_equiv 2 14 :=
begin
unfold mod_12_equiv, apply rfl,
end

/-
Let's prove that the whole infinite
set of values of the form n + k * 12
is congruent.
-/
example : 
    ∀ k : ℕ, ∀ n : ℕ, 
    mod_12_equiv n (n + k * 12) :=
begin
intros,
unfold mod_12_equiv,
-- The simp tactic uses many rules to simplify expressions,
-- and can prove them true when trivial would do so
simp,
end

/-
Let's show that mod_12_equiv is an equivalence
-/

example : reflexive mod_12_equiv :=
begin
unfold mod_12_equiv,
unfold reflexive, -- EX: why just x here?
intro, apply rfl,
end

example : symmetric mod_12_equiv :=
begin
unfold symmetric,
intros x y,
unfold mod_12_equiv,
intro h,
-- New tactic: rewrite using an equality
rw h,
end

example : transitive mod_12_equiv :=
begin
unfold transitive,
intros x y z xy yz,
unfold mod_12_equiv at xy,
unfold mod_12_equiv at yz,
unfold mod_12_equiv,
rw xy, assumption,
end 


/-
In the rest of this file, we transition
from x R y notation to x ≺ y. You will 
find both used in mathematical writing.
Be careful not to read x ≺ y as saying
that x is less than y. The ≺ symbol in
this context can refer to any relation
whatsoever.
-/

/-
We now define additional properties of
binary relations on a set. For each of
them, come up with one or more familiar
relations having these, and not having
these, properties.
-/

def total := ∀ x y, x ≺ y ∨ y ≺ x

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def connected := ∀ x y, x ≠ y → x ≺ y ∨ y ≺ x

variable {α : Type} 

def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

/-
A relation is conceptually similar to a set of 2-tuples.
However, the syntax is different.
-/

def mod_12_equiv': set (ℕ × ℕ) :=
  {tuple | tuple.1 % 12 = tuple.2 % 12}

/-
This won't work:
def mod_12_equiv'': set (ℕ × ℕ) :=
  λ x y, x % 12 = y % 12
-/

#reduce ∃(n m: ℕ), (n, m) ∈ mod_12_equiv'

example: ∀(n m: ℕ), mod_12_equiv n m ↔ (n, m) ∈ mod_12_equiv' :=
begin
  assume n m,
  apply iff.intro,
    unfold mod_12_equiv,
    assume pf_mod_12_equiv,
    unfold mod_12_equiv',
    assumption,

    unfold mod_12_equiv',
    assume pf_mod_12_equiv',
    unfold mod_12_equiv,
    assumption
end

def set_of_tuples_to_relations: set (β × β) → (β → β → Prop) :=
begin
  assume s,
  exact (λ x y, (x, y) ∈ s)
end

/-
Let us define a relation R as R1
For example imagine the relation “is one or two less than”
as defined over the naturals.
It contains the 2-tuples {(0, 1), (0, 2), (1, 2), (1, 3),
 (2, 3), (2, 4), (3, 4), (3, 5), etc.}

Now let us define R2 (or R ◦ R) as the relation having
left-hand elements equal to the left-hand elements of the
tuples in R1, and right-hand elements equal to the
corresponding right-hand elements of the right-hand elements
in R1
E.g., from above this would be “is two, three, or four
less than”
It contains the 2-tuples {(0, 2), (0, 3), (0, 4), (1, 3),
 (1, 4), (1, 5), etc.)

R3 (or R ◦ R2) is the relation having left-hand elements
having left-hand elements equal to the left-hand elements
of the tuples in R1, and right-hand elements equal to the
corresponding right-hand elements of the right-hand
elements in R2
E.g., from the above this would be “is three, four, or
five less than”
-/

def successor: (β → β → Prop) → (β → β → Prop) :=
begin
  assume r,
  exact λ(x y: β), ∃(b: β), (r x b) ∧ (r b y)
end

/-
Transitive closure. 
Transitive closure is the union of R and all
of its successor relations

We're not ready for the following formal definition
of the transitive closure of a relation, as we
haven't covered inductive definitions, but we can
introduce the idea informally now.
-/

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c


/-
The following material is optional and will not be
tested.
-/

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁

end relation_2102_sec

end relation_2102_ns
