********
Equality
********

Equality
========

Equality is a binary relation that associates every value of every
type with itself and no other value.  Example include :math:`0 = 0`, 
:math:`true = true`, and :math:`"Hi" = "Hi"`.

We make this idea precise with an inference rule, a rule that gives us
a way to obtain proofs propositions, here assertions that two things
are equal. Informally, given any type, T, and any value, t : T, of t
this type, you can contruct a proof, (eq.refl t), of the proposition,
t = t. If you need a proof of t = t, this rule gives you a way to get
one: apply eq.refl to T (a type) and t : T, a value of type T. We can
write this inference rule like this:

.. raw:: html

  <img src="_static/eq.reflx.png">

.. raw:: latex

  \begin{prooftree}
    \AxiomC{T : Type, t : T}
    \RightLabel{eq.reflx}
    \UnaryInfC{t = t}
    \singleLine
  \end{prooftree}



As an example, the term, (eq.reflx nat 0), obtained by applying
eq.reflx to the type, nat, and the value, 0 (of type nat) is a
proof of the proposition, 0 = 0.


EXERCISE: Explain in a sentence or two why this rule never derive a
proof of the proposition that 0 = 1?

Note that the the value of T can be inferred from the value of t, as
Lean knows the type of every term. In principle we should be able to
write (eq.refl 0) and have Lean figure out that the value of the now
{\em implicit} argument, T. When writing inference rules we surround
arguments with curly braces that we want to be inferred from context
rather than given explicitly by the programmer.

   { T: Type }, t : T
  ------------------- (eq.refl)
  (eq.refl t) : t = t


EXERCISE: Bind the identifier, zeqz, to a proof of 0 = 0.


.. code-block:: lean

	def zeqz : 0 = 0 := (eq.refl 0)

Types
=====


Above the line in this inference rule, we meet a 
new kind of judgment here: a type judgment. If X 
is some type (such as string, bool, or nat), and 
x is a value of that type, X, we can denote this 
fact by writing x : X. We read this as "x is of 
type X."

The Lean tool, which you're using, is based on a
foundational theory called type theory. In type
theory, every object (value) and every expression 
has a type. Every parameter, such as an argument 
to a function, has a type, as does the value that
a function returns. Every well formed expression 
has a unique type. 

In Lean you can check the type of an expression
by using the #check command. 
-/

#check 0
#check "Hi!"
#check tt

/-
Note that ℕ is math shorthand for the type of 
natural numbers, i.e., non-negative integers 
(thus zero on up). Hover your mouse over the 
#check commands to see what are the types of 0,
"Hi!", and tt in Lean.
-/

/-
Now here's an amazing idea. In Lean, types are 
values, too! It thus follows that a type must 
have a type. So what is the type of a type? Well,
let's check a few!
-/

#check nat
#check bool
#check string

/-
Partial answer: The type of any ordinary data
type is simply "Type".

Now the curious and insightful student will ask,
"Well, then, what about Type, itself? Is it a value?
What is its type?"
-/

#check Type
#check Type 1
#check Type 2
-- etc!

/-
So, if T is some data type, then we'd write the
type  judgment, "T : Type". And if T is a type, 
and t a value of type, T, then we'd write t : T. 
-/

/-
With all that out of the way, we can once again 
write and now more fully understand the inference 
rule for equality that we really want. 

T: Type, t : T
-------------- (eq.refl)
  pf: t = t

Those are now type judgments above the line. You can 
understand this inference rule as saying this: "if you 
give me a T that is a type (e.g., bool, nat, string), 
and if you also give me a value, t, of that type, T, 
(e.g., 0 or true), I will give you back a proof that 
t = t. 

This single inference rule thus defines a very sensible notion of equality for all values of all types that now
exist or might ever be defined. 

So now, rather than a separate axiom for 0 = 0,
another one for 1 = 1, another for true = true, and
yet another for Fido = Fido, so forth, we have one 
a single inference rule that derives them all as
special cases, one case for every possible value,
and type of, t.

You can think of the "inputs" above the line as 
parameters. That is how we generalize from a single
case to an infinity of cases.

/- * Inference rules as computations * -/

Indeed, you can now start to think of eq.refl in
two different ways: as a logical inference rule,
and as a kind of program! This program takes two
arguments. The first is a type and the second is 
a value of the type given as the first argument.
The program then returns a proof that the second
argument is equal to itself. 

We are given this inference rule as something 
akin to an axiom, in the sense that it does not
require proofs of other propositions as arguments.
The only "proofs" it requires as inputs are proofs 
that T is a type and t is a value of that type. 
That is, its inputs are not proofs of proposition,
but rather are type judgments. 

EXERCISE: Take the view that eq.refl is a program
that takes two parameters as discussed here, and
write an expression that reduces to ("returns") a 
proof of the proposition that the natural number, 
0, is equal to itself. 

EXERCISE: Give comparable expressions that return
proofs of equality-with-self for the Boolean value, 
tt, and for the string value, "Hello Lean".
-/


Type Inference
==============

/- Type Inference -/

/-
Now as we've seen, given a value, t, of some type, 
T, Lean can tell us what T is. The #check command
tells us the type of any value or expression. The
key observation is that if you give Lean a value,
Lean can determine its type. 
-/

#check 0

/-
We can use the ability of Lean to determine the
types of given values to make it easier to apply
the eq.refl rule. If we give a value, t, as an
argument, Lean can automatically figure out its
type, T, which we means we shouldn't have to say
explicitly what T is.

EXERCISE: If t = 0, what is T? If t = tt, what is
T? If t = "Hello Lean!" what is T?

Lean supports what we call type inference to 
relieve us of having to give values for type
parameters explicitly when they can be inferred
from from the context. The context in this case
is the value of t.

We will thus rewrite the eq.refl inference rule
to indicate that we mean for the value of the T
parameter to be inferred. We'll do this by putting
braces around this argument.  Here's the rule as 
we defined it up until now.

T: Type, t : T
-------------- (eq.refl)
  pf: t = t

Here's the rewritten rule.

{ T: Type }, t : T
------------------ (eq.refl)
    pf: t = t

The new version, with curly braces around 
{ T : Type }, means exactly the same thing,
but the curly braces indicates that when 
we write expressions where eq.refl is 
applied to arguments, we can leave out the 
explicit argument, T, and let Lean infer it
from the value for t.

What this slightly modified rule provides is 
the ability to expressions in which eq.refl is 
applied to just one argument, namely a value, 
t. Rather than writing "eq.refl nat 0", for 
example, we'd write "eq.refl 0". A value for 
T is still required, but it is inferred from 
the context (that t = 0 so T is of type nat), 
and thus does not need to be given explicitly.
-/

/-
In Lean, the eq.refl rule is defined in just
this way. It's even called eq.refl. It takes 
one value, t, infers T from it, and returns a 
proof that that t equals itself! 

Read the output  of the following check command 
very carefully. It says that (eq.refl 0) is a
a proof of, 0 = 0! When  eq.refl is applied to 
the value 0, a proof of 0 = 0 is produced.
-/

#check (eq.refl 0)

/-
EXERCISE: Use #check to confirm similar conclusions
for the cases where t = tt and t = "Hello Lean!".

EXERCISE: In the case where t = tt, what value does
Lean infer for the parameter, T?
-/


Propositions as Types
=====================

/-
Wait! Lean is telling us that: eq.refl 0 : 0 = 0.
Putting parenthesis in can make it easier to read:
(eq.refl 0) : (0 = 0). We've so far read this as 
saying that (eq.refl 0) is a proof of 0 = 0. But 
the observant reader will see that it looks just 
like a type judgment as well. It looks like it's 
saying that (eq.refl 0) is a value of type (0 = 0).

And indeed that is exactly what it's saying. Here
is the deep idea: in the "constructive logic" of 
Lean, propositions are formalized as types, and 
proofs are represented values of these types! 

A proof, then, is valid for a given proposition
if it is a value of the corresponding type. And
Lean's type checker can always determine whether 
that is the case! In lieu of human checking of
the validity of proofs, we therefore now have a 
mechanical proof checker!

Read the eq.refl inference rule again. We can 
now see it clearly as defining a computation. 
It can now be seen as saying, "if you give me 
any value, t, I will infer its type, T, and will 
construct and return a value of type, t = t. 
Not only that but the type-checker will provide 
you with a very high degree of assurance that 
it's a valid proof! 
-/

/-
We can also now understand what it means when we
say that Lean is a proof checker. It means that
Lean will not allow us to use proofs that are not
valid with respect to the propositions/types they 
are said to prove, because they won't type check.
-/

/-
Let's look at type checking a little more deeply.
We can always assign to a variable a value of the 
type that the variable is declared to have. 
-/

def n : nat := 1

/-
This Lean definition says that n is a variable 
for which a value of type nat must be provided
(n : nat), and it goes on to assign to n ( := )
the value 1. 
  
The Lean type checker checks that 1 is a
value of type nat, which it is. Lean therefore
accepts the definition, and consequently n is 
defined, with the value, 1, for the remainder 
of this file.
-/

/-
EXERCISE: Define s to have the type, string,
and the value, "Hello, Lean!"
-/

/-
We note that we could have elided the explicit
type declaration (n : nat), as Lean infers from 
the value, 1, on the right, that the intended 
type of n can only be nat.
-/

def n' := 1
#check n'

/-
EXERCISE: define s' to be "Hello, Lean", leaving
it to Lean to infer the type of s'.
-/

/-
The type checker also absolutely prevents the
assignment to a variable of a value that is not
of the right type. Read the following code and
identify the type error, then uncomment it and
see how Lean detects and reports the error. Be
sure you understand the error message. This one
is self-explanatory.
-/

-- def n'' : nat := "Hello Lean!"

/-
Now let's replace the "nat" type with the
type "0 = 0." Remember, every proposition is
now viewed as a type. We could thus similarly
declare a variable, p, to have this type, just
as we declared n to have type nat. Finally we
would need to assign to p a value of this type,
which is to say a proof of 0 = 0. Compare this 
code carefully with that for n, above. Note 
the deep parallels. Here, however, rather than
assigning a value such as 1, we're assigning 
a value that is a proof, and it, in turn, is
produced by applying the eq.refl inference
rule to the value 0.
-/

def      p     :  0 = 0   :=   (eq.refl 0)
/-    variable    type    bind  value/proof   
-/

#check p    -- what is the type of p?
#reduce p   -- what is the value of p?

/-
EXERCISE: To the variable s, bind a proof of
the proposition that "Hello Lean!" is equal 
to itself.

EXERCISE: Do the same for the Boolean value,
tt.
-/

/-
And just as the type checker prevents the
assignment of a value that is not of the
right type to a variable such as n, so it
also prevents the assignment to p of a
proof that is not of the right type. 
-/

/-
EXERCISE. Explain precisely why Lean 
reports an error for this code and what
it means. (Uncomment the code to see the
error, then replace the comments so that
the error isn't a problem in the rest of
this file.)
-/

-- def p' : 0 = 0 := (eq.refl 1)

/-
EXERCISE: Explain why could you never use
eq.refl to successfully produce a proof
of 0 = 1? Explain.
-/

/-
In Lean and related proof assistants,
propositions are types, proofs are values
of proposition types, and proof checking 
*is* type checking. Put a start next to
this paragraph and be sure that you
understand it. It takes time and study
to fully grasp these concepts.
-/

/-
EXERCISE: Prove the following theorem,
teqt, that 2 = 1 + 1. Try using eq.refl.
-/

/-
That last proposition, 2 = 1 + 1, is a bit
different because it has different terms on
each side of the equals sign. In Lean, these
terms are reduced (evaluated) before they are
compared, and so eq.refl can still be used 
to prove this proposition. 
-/


/- * What is the type of a proposition? *-/

/-
We've already seen that types are values, 
too, and that a type thus has a type. The
type of nat is Type, for example. So, in 
Lean, what is the type of a proposition, 
such as 0 = 0? Let's find out using #check. 
-/

#check (0 = 0)

/-
EXERCISE: What is the type of (0 = 1)?
Answer before you #check it, then #check 
it to confirm.

EXERCISE: What is the type of "Hello Lean" =
"Hello Lean"?
-/

/-
Lean tells us that the type of each proposition is
Prop. In Lean, every logical proposition is of type
Prop, just as every ordinary computational type, such
as nat, bool, or string, is of type, Type. So how
do Prop and Type relate? Where does Prop fit in? 
What is its type? What is the type of Prop? We can 
of course just #check it!
-/

#check Prop

/-
Ah ha. Prop is of type Type, which is to say that 
that Prop is of type, Type 0. We thus now have a
complete picture of the type hierarchy of Lean.

Prop   :   Type : Type 1 : Type 2 : Type 3 : ...
  |          |
0 = 0       nat
  |          |
eq.refl 0    1

Prop is the first type in the hierarchy. Every
propositional type is of type Prop. We illustrate
here that the type (0=0) is of type Prop, but so
is 0 = 1, 1 = 1, tt = tt, and so are all of the
other propositions we'll ever see in Lean. All 
propositions, which again are themselves types,
are of type Prop in the logic of Lean.

By contrast, computational types, such as nat,
but also string, bool, and function types (we
will see them soon enough) are of type, Type.

The lowest layer in the diagram illustrates
where values fit in. The proof, eq.refl 0,
is a value of type (0 = 0), just as 1 is a
value of type nat.

We will never need types above Type in this 
class. Mathematicians, logicians, and program
verification experts who use Lean and other tools
like it do sometimes need to be careful about how
values fall into the various "type universes,"
as these various levels are called. 
-/


More Type Inference
===================

/-
In Lean and related proof assistants, such
as Coq, you can obtain proofs not only by
applying inference rules, such as eq.refl,
directly, but also by using programs, called
tactics, that automate some of the details
of finding and applying inference rules or
sequences of such rules.

As an example, we look at the "rfl" tactic,
which slightly simplifies the application of
the eq.refl inference rule. Let's first look
at a few uses of rfl.
-/

theorem t1 : 2 = 1 + 1 := rfl
theorem t2 : tt = tt := rfl

/-
The rfl tactics appear to be producing
proofs of the given propositions, and that
is indeed the case. If we #check t1 we'll
see that this is so. t1 is a proof of 0=0
and in fact is exactly eq.refl 0.
-/

#check t1
#reduce t1

/-
What rfl is doing is grabbing the left side
of an equality proposition, such as 2 or tt
in the examples here, and returning eq.refl
applied to that value.
-/

/-
EXERCISE: Use rfl to produce a proof, h, of
the proposition, "Hello" = "He" ++ "llo".

EXERCISE: Use rfl to prove p: 3*3+4*4=5*5.
-/

/- * A brief aside about terminology *-/

/-
Note: The word "theorem" in mathematics is generally
used to mean an "important" proposition that has been
proved. The word lemma is used to mean a less 
important proposition that has been proved, often as
part of a larger proof of a more important theorem.
Mathematicians also use the word corollary to refer
to a proposition the proof of which follows from the
proof of a more important theorem. You can read all
about the various words used to refer to things that
have been proved, or that are intended to be proved,
here: https://academia.stackexchange.com/questions/113819/is-it-acceptable-for-a-referee-to-suggest-changing-theorem-into-proposition.
For our purposes, we'll typically just use theorem.
-/

/-
As you have now seen, Lean's notion of equality
does not mean exact equality of expressions. It
means instead the equality the values to which 
they "reduce" when you "evaluate" them. We can 
prove 2 = 1 + 1 using rfl (or eq.refl of course) 
because the "literal expression", 2, reduces to 
the value 2; the function application expression, 
1 + 1 (wherein the plus function is applied to 
the two arguments, 1 and 1) also reduces to 2;
those two values are the same; and so eq.refl 2
generates a proof that type-checks. 
-/

/- 
EXERCISE: Prove as a theorem, tthof (a silly and 
uninformative name to be sure), that 2 + 3 = 1 + 4.

EXERCISE: Prove as a theorem, hpleqhl, that "Hello " 
++ "Lean! is equal to "Hello Lean!" (these values 
are of type string in Lean and the ++ operator here 
refers to the string concatenation function in Lean.)
-/


Properties
==========

/-

HOMEWORK: Read, complete, submit.

We've seen that equality is reflexive.
That is, everything is equal to itself.

It is also symmetric in the sense that
if any value, a, is equal to some other
value, b, i.e., if a = b, then b is also
equal to a, i.e., b = a. 

What this means is we have an inference 
rule that both expresses the symmetric
property of equality and allows us to 
compute a proof of b = a from any proof 
of a = b, no matter what a and b are (no 
matter what type, T, a and b have, and 
no matter what values they have of this
type).
-/

/-
  (T: Type) (a b: T) (ab: a = b)
  ------------------------------ (eq.symm)
           ba: b = a

-/

-- Let's see it in action in five lines
def a := 1
def b := 2 - 1
lemma ab : a = b := rfl 
#check ab           -- a proof of a = b
#check (eq.symm ab) -- a proof of b = a!

/-
This is a big success. We understand not
only the property of being symmetric but
that we can use symmetry to derive new
proofs from proofs that we already have.
In fact, eq.symm is a program that does
just this derivation, as we see here!
-/

/-
Finally we come to the notion that
equality is also transitive. That means 
that for any values, a, b, and c, if 
a = b, and if b = c, then it must be 
that consequently a = c as well. 

  {T : Type}, 
  { a b c: T },
  ab: a = b, 
  bc: b = c
  ------------ (eq.trans)
   ac: a = c

That is, if given proofs of a = b and 
b = c, eq.symm constructs and returns 
a proof of a = c. 

Let's see it in action. We've already
got variables a and b to work with. We
need one more, c.
-/

def c := 1

/-
We've also already got a proof of a = b.
It's easy to generate one of b = c. 
-/

lemma bc : b = c := rfl

/- 
And now we can apply eq.trans to these
two premise-proofs and it will construct
and return a proof of the conclusion. The
expression that applies eq.trans to these
two proofs is (eq.trans ab bc). Now for
the fun part!
-/

#check eq.trans ab bc


/-
EXERCISE: First write a textual inference
rule, let's call it eq_snart. It says that
if T is any type; if a, b, and c are values 
of this type, T; and you are given proofs  
of a = b and c = b then you can  derive a 
proof of a = c. 
-/

/-
EXERCISE: Now "prove" that this rule is
valid by implementing it as a program 
that, when given any argument values of 
the specified types, returns a proof of 
the specified type (of the conclusion). 

Hint: Use eq.trans to construct the proof
of a = c. It's first argument will be ab, 
the proof that a = b. It's second argument
has to be a proof of b = c for it to work
to derive a proof of a = c; but all we've
got is a proof of c = b (in the reverse
order). How can we pass a second argument 
of type b = c to eq.trans, so that it can 
do its job, when we have at hand is a proof 
of c = b. Now a major hint: we already
have a way to construct a proof of b = c
from a proof of c = b. Just use it. 

Ignore the error message in the following 
incomplete code. The problem is simply 
that the definition is incomplete, due 
to the underscore placeholder. Replace 
the underscore with your answer. Leave 
parenthesis around your expression so
that it gets evaluated as its own term. 
-/


def eq_snart    { T : Type} 
                { a b c: T }
                (ab: a = b)
                (cb: c = b) :=
    eq.trans 
        ab 
        (_)

/-
EXERCISE: Use lean to implement a new 
rule that that, from a proof of c = b 
and a proof of b = a, derives a proof 
of a = c. Call the proof eq_snart' 
(why not, it sounds funny).
-/


/-
EXERCISE: Use eq_snart rather than eq.trans directly to prove a = c, 
given proofs of a = b and c = b.
-/

lemma cb : c = b := rfl
#check cb
theorem aeqc : a = c := eq_snart _ _

/-
In general, there are many ways to prove 
a given theorem. Each distinct proof is 
nevertheless an inhabitant of the type of
the proposition that it proves, and each
suffices as evidence to justify a truth
judgment for the proposition. In cases
where one's aim is simply to prove a
proposition, the particular proof object 
that is used doesn't matter. We say that
the particular proof is "irrelevant."
-/ 

/-
SUMMARY: In this section (1) you first
recalled  that the equality relation is 
reflexive, symmetric, and transitive. 
(2) You saw that in Lean, these are not 
just abstract ideas; there are also  
inference rules that you can apply to 
to arguments of the right types to 
build proofs of new propositions. (3) 
You also saw that you can prove your own
inference rules by writing programs that
implement them! Such programs can use
already accepted inference rules (such
as eq.refl, eq.symm, eq.trans) in their
implementations. Thereafter, the new 
rules are as good as the old, and can 
then also be used to construct proofs 
that might be needed.
-/


Tactics
=======

/-
We've already seen that we can assert
that a proposition is true by defining
a variable to have that proposition as
its type, and we can prove the proposition
by assigning a proof term to the variable.
-/

lemma zeqz : 0 = 0 := eq.refl 0

/-
Sometimes it's harder to write an exact
proof term (here, eq.refl 0). In these
cases it can help to figure out a proof
term step by step. Lean supports step
by step development of proof terms with
what are called tactic-based proving.
Here's an equivalent tactic-based proof.
-/

lemma zeqz' : 0 = 0 :=
begin
  apply eq.refl 0,
end

/-
In this case, the proof is so simple
that writing a script is more work.
The key thing to see here, though, is
the "apply" tactic. It applies some
already known rule, here eq.refl, to
move from a state in which something
is to be proved to a state in which
something new has been proved.
-/

/-
Now open the Lean Messages panel by typing
control-shift-enter or command-shift-enter
(Windows/Mac). Now place your cursor first
at the start of the "apply". The message
window will display the "tactic state" at
this point in the script. The state say
that nothing is assumed and the remaining
goal to be proved is 0 = 0. Now move your
cursor to the next line, before the "end."
The tactic state is empty, nothing is left
to be proved, QED. 
-/


/-
EXERCISE. Define zeqz'' as also
being of type 0 = 0, but after the :=,
just write begin on the next line and 
then an end on the following line. You
need to type the begin and end lines
before continuing.
-/


/-
HOW TO SOLVE IT:

Initially there will be an error. Hover
over the red squiggle under the "end."
It tells you that you haven't yet proved
something that remains to be proved, and
it tells you what remains to be proved.
 
Insert a blank line between the begin and 
end. The tactic state tells you what is
known at a given point in a tactic script
(before the turnstile character, ⊢, and 
what remains to be proved, after. Here, 
the goal that remains is 0 = 0. 

If you then click on the next line, end, 
Lean tells you that the proof-generating 
tactic script between the begin and end
lines failed because some goal remains to 
be proved.

In general, a tactic will only partially 
prove a goal, leaving some parts still to 
be proved. In such cases, more tactics 
are then used to finish the construction 
of the required proof. Tactic commands
are separated by commas. We'll see more
later. 

Go ahead and type the required tactic  
between begin and end. Click on the 
line with the tactic, then on the end. Watch how the tactic state changes as 
you go from line to line. 
-/


/-
You might have noticed that while "apply
eq.refl 0" finishes the proof, so does 
just "apply eq.refl". In this case, Lean
infers both arguments to eq.refl from 
context. That, in fact, is what rfl does.
It's not technically a tactic. It is just
using type inference to infer both of the
arguments needed for eq.refl!

Some people refer to such a script as a
proof. A better way to think about it is 
as a step-by-step recipe for building a 
proof. The actual proof at the end of the
day is the proof object that the script
constructs: eq.refl 0, in this case.
-/

