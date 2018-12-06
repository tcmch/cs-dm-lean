/-
Homework #7. Proper subset. 
-/

/-
We have studied the subset relation on
sets. A set x is said to be a subset of
y if ∀ e, e ∈ x → e in y. 

By contrast, we say that x is a *proper* 
subset of y if x is a subset of y and 
there is some f in y that is not in x.
Here's a formal definition of this binary
relation on sets.
-/

def proper_subset : 
  ∀ { α : Type }, 
    set α → set α → Prop :=
  λ α x y, forall (e : α), 
    (e ∈ x → e ∈ y) ∧ (∃ f, f ∈ y ∧ f ∉ x) 

/-
Your homework, should you choose to 
complete it (in preparation for the
postponed quiz), is to use "example" 
to assert and prove the proposition
that { 1, 3 } is a proper subset of 
the odd numbers. 
-/


/-
We now introduce some new concepts
to help you through this proof. The
first has to do with the direction
of rewriting, the second explains
what the cases tactic actually does
and shows how it can then be used to 
do false elimination on hypotheses
that assert incorrect equalities. We 
will also remind you about how to 
deal with an assumed proof of the
form, e ∈ ∅, which is obviously a
contradiction. 
-/

/--/
First, a note on the rewrite tactic.

If e : x = y is an assumed proof of 
x = y, then the tactic, "rewrite e" 
rewrites each occurence of x in the
goal with y. Click through the proof
of the following trivial proposition
to see the idea in action.
-/

example : 
  ∀ a b c : ℕ, a = b → b = c → a = c  
:=
begin
intros a b c,
assume ab bc,
rewrite ab,
rw bc, -- shorthand
-- rw does "apply rfl" for us automatically
end

/-
If you want the rewriting to go in 
the other direction, use "rw ←e"
-/

example : 
  ∀ a b c : ℕ, a = b → b = c → a = c  
:=
begin
intros a b c,
assume ab bc,
rewrite ←bc,
rw ←ab, 
end


/-
Second, let's talk more about cases.

Whenever we have any data value, even
if its a proof, it must have been built
by one of the constructors defined for 
that type of data.

With natural numbers, for example, a
given ℕ must be either 0 (constructed
by nat.zero) or 1 + a smaller natural
number (built by applying nat.succ to 
the next smaller ℕ).

So if we have some value, n : ℕ, 
even though we don't know what its
value is, we do know there are only 
two ways it could be been produced. 
So, if we want to prove something 
about n, it suffices to show it is
true no matter which constructor 
was used to "build" n. Case analysis 
(and the cases tactic) replaces an 
assumed value in the context with
each of the constructors that could
have been used to build it. Click
through the following proof to see
how this plays out, not when we 
apply cases to a disjunction, but 
to a natural number.
-/

example : ∀ n : ℕ, true :=
begin
assume n,
cases n,  -- whoa, that's cool
trivial,
trivial,
end

/-
The same idea holds for values that
are proofs. Suppose we have a proof 
of, say, a disjunction, P ∨ Q. There
are only two ways that proof could
have been built: by or.inl or or.inr.
So when we use cases on a proof of a
disjunction, even though we don't
know exactly how it was proved, if
we can prove our goal for each of
the two ways in which it *could* have
been built, then we've proved our 
goal in either case, as there are no
other ways in which we could have had
the value in the first place.
-/

example : ∀ P Q : Prop, P ∨ Q → true :=
begin
intros P Q,
assume h,
cases h, -- whoa, now I get it!
trivial,
trivial
end

/-
Okay, so here's the cool thing. If you
end up with an assumption, such as 2 = 3,
in your context, which is to say a wrong
proof of an equality, you can do case 
analysis on it. We've already seen that 
there is only one way to construct a proof 
of an equality, using eq.refl applied to one 
value. So if you have assumed a proof 
of 2 = 3, when you do case analysis on 
it, Lean will see that there are *no*
constructors that could have been used
to construct that proof. You thus have
zero cases to prove and you're done! It
is almost magic. But it's not. Having no 
cases to prove is just false elimination 
under a different guise.
-/

example : 4 = 5 → 0 = 1 :=
begin
assume four_equals_five,
cases four_equals_five, --whoa!
end

/-
Third if you have an assumption of 
the form, h : e ∈ ∅, remember you 
can use have f : false := h. That
gets you what you need to be done. 

Oh, and don't forget that e ∉ x is
the same as ¬ (e ∈ x), and that of
course is just (e ∈ x) → false. Or,
just try cases!

And here are a few final hints. 

(1) Remember that a set in Lean is 
really represented as a membership
predicate.

(1A) When a set, such as { 1 , 3 }, 
viewed as a membership predicate, 
is applied to a value, it reduces 
to a proposition, here in the form 
of a disjunction. So of you end up 
with something like e ∈ { 1, 3 } as
an  assumption, treat it as a proof 
of a disjunction.

(1B) If you end up with a goal of 
the form of a membership proposition,
such as the following, for example,

α ∈ {n : ℕ | ∃ (m : ℕ), n = m }

think of it as the application of 
the predicate/function defined by 
the set, taking argument, n, to α. 
The overall expression reduces to 
∃ (m : ℕ), α = m. You need to see
this to know what inference rule 
to use to prove such a goal.
-/

example : 
proper_subset  
  { 1, 3 } 
  { n | ∃ m, n = 2 * m + 1 } 
:=
begin
unfold proper_subset,
intro e,

split,

-- subset
assume h,
cases h,
show ∃ m, e = 2 * m + 1,
apply exists.intro 1, assumption,

cases h,
apply exists.intro 0, assumption,

cases h,

/-
have f : false, from h,
contradiction,
-/
-- proper
apply exists.intro 5,
split,
show ∃ m, 5 = 2 * m + 1, 
apply exists.intro 2, apply rfl,

intro h,
change 5 = 3 ∨ 5 = 1 ∨ false at h,
cases h,
cases h,
cases h,
cases h,
cases h,
end
