************
Introduction
************

This course teaches discrete math in large part through its uses in
software *specification* and *verification.* The aim is to make the
abstract ideas of discrete mathematics come alive by showing how they
play out in the context of automated tools for formal, which is to say
mathematical and logical, reasoning about software. Let's get started.

Specification, Implementation, Verification
===========================================

Software is an increasingly critical component of major societal
systems, from rockets to power grids to healthcare, etc. Failures are
not always bugs in implementation code. The most critical problems
today are not in implementations but in requirements and
specifications.

* **Requirements:** Statements of the effects that a system is meant to have in a given domain
* **Specification:** Statements of the behavior required of a machine to produce such effects
* **Implementation:** The definition (usually in code) of how a machine produces the specified behavior

Verification and Validation
===========================

Avoiding software-caused system failures requires not only a solid
understanding of requirements, specifications, and implementations,
but also great care in both the *validation* of requirements and of
specifications, and *verification* of code against specifications.

* **Validation:** *Are we building the right system?* is the specification right; are the requirements right?
* **Verification:** *Are we building the system right?* Does the implementation behave as its specification requires?

Natural and Formal Languages
============================

You know that the language of implementation is code. What is the
language of specification and of requirements?

One possible answer is *natural language*. Requirements and
specifications can be written in natural languages such as English or
Mandarin. The problem is that natural language is subject to
ambiguity, incompleteness, and inconsistency. This makes it a risky
medium for communicating the precise behaviors required of complex
software artifacts.

The alternative to natural language that we will explore in this class
is the use of mathematical logic, in particular propositional logic,
first-order predicate logic, set theory, and higher-order constructive
logic.

Mathematical Logic
==================

A logic is a language of *propositions*, which are assertions that
certain *states of affairs* hold in certain *domains of discourse.*
For example, a proposition might assert that at a certain point in the
execution of a program it is necessarily the case that the value of
some variable, *x*, is non-zero. Here the domain of discourse is that
of the states of a program. Another proposition might assert that Jane
is the mother of Bob.

A logic, as a language of propositions, is also rooted in the notion
of *truth*. A proposition is subject to being *judged* to be true, or
not. For example, if, on every possible execution path from the start
of a program, through sequences of statements including conditionals
and loops, to a point of interest, a variable, *x* is set to a value
that is non-zero, then one could judge as true the proposition that
the value of *x* at that point is non-zero. Similarly, if Jane really
is the mother of Bob in a situation of interest, then th proposition
that she is could also be judged to be true.

Propositions are mathematically precise statements that assert that
certain states of affairs hold in given domains of discourse, and as
such are subject to being judged to be true, or not. In mathematical
logic, the condition under which a proposition can be judged to be
true is that there is a *proof* that it is true. One of the primary
aims of this course is to work up to a deep understanding of what is
meant by a proof of a logical proposition.


Many Logics
===========

There are many logics. Different logics are able to express different
kinds of propositions, and in different ways, and each comes with its
own particular concepts and forms of proofs. In this course, students
will first see first-order predicate logic *in use* as a language in
which to write and verify propositions about programs. Next, students
will delve into the nature of logic and truth by studing the simplest
of useful logics: propositional logic. From there, the course builds
to the concept of inference rules as valid principles that capture
natural forms of reasoning. Having seen the uses of predicate logic,
students then study its nature, its syntax and semantics. Finally,
students learn about proofs and their construction, again supported
by software tools, using the higher-order constructive logic of the
Lean Prover. 

Propositional Logic
===================

Propositional logic is a language of simple statements. For example,
*Tennys plays tennis* is an *elementary proposition*. It is also true
if by *Tennys* we mean the person who recently played in the French
Open.  *Tennys is from Tennessee* is another elementary proposition,
and one that is also true of that same person. And because these two
propositions are true, so is the *compound* proposition that *Tennys
is from Tennessee and Tennys plans tennis*. Proposition logic is a
very simple logic: of elementary propositions that can be judged to be
either true or false, and compound propositions built by connecting
smaller propositions together using the logic connectives, *and, or,
not* and others. The truth of a compound proposition in propositional
logic is judged by (1) the truths of its constituent parts, and (2)
the connective used to build it out of its immediately smaller parts.
If you see an immediate connection between propositional logic and
Boolean expressions, you have seen the light: these languages are for
out intents and purposes the essentially the same.

Predicate Logic
===============

Sometimes we want to talk about whether this person, or that person,
or some other person plays tennis. To this end, we imagine a logic in
which propositions can have parameters. If we replace the individual
person, *Tennys*, in the proposition, *Tennys plays tennis*, with a
variable, *P*, that can take on the identify of any person, then we
end up with a parameterized proposition, *P plays tennis*. We call
such a parameterized proposition a *predicate*. Predicate logic is a
language of propositions and predicates, which you can think of as
functions that, when given parameter values, new propositions. Such
propositions might again be true or they might not be. We can now
think of *plays tennis* as a predicate, or as a *property* that any
invidivual either has or not. For example *PlaysTennis(Tennys)* might
be the proposition, *Tennys plays Tennis* while *PlaysTennis(Kevin)*
might be the proposition *Kevin plays Tennis*. For each possible
person name, *P*, there is a proposition, *PlaysTennis(P)*.

Predicate logic also allows one to write *quantified* propositions
using existential and universal quantifiers. For example, one might
write a proposition stating that *there exists some person, P, such
that PlaysTennis(P)*, an existentially quantified proposition; or that
*for every person, P, PlaysTennis(P)* (colloquially, *everyone plays
tennis*).

We note briefly, here, that, like functions, propositions can have
multiple parameters. For example, we can generalize from *Tennys plays
Tennis and Tennys is from Tennessee* to *P plays tennis and P is
from L,* where the variable, *P*, ranges over people and the variable,
*L* ranges over locations.

While a predicate with one parameter can be thought of as a *property*
of the individuals to which it applies (whether someone plays tennis
or not), a proposition with two or more parameters can be thought of
as a *relation*, here betwen people who play tennis and places where
they live. A property picks out individuals for which a corresponding
proposition is true, while a relation picks out pairs (or larger sets)
of individuals for which corresponding propositions are true.

For example, the *pair* (Tennys, Tennessee) is in the relation picked
out by this parameterized proposition, but (Kevin, Tennessee), is not,
because Kevin is from New Hampshire, so the proposition *Kevin plays
tennis and Kevin is from Tennessee* is not true. 


Logic and Code
==============

Predicate logic is the logic of everyday computer science, and of the
programming system and language that we will be using to learn how to
read, write, and use predicate logic. Dafny supports not only coding
in an ordinary imperative (Python or Java-like) language, but also the
use of predicate logic and what we will learn are pure functional
programs to write *specifcations.* Specifications are propositions
that desribe precisely how given programs must behave. Dafny has an
underlying mechanism for then judging whether such propositions are
true, and it gives programmers real-time feedback on whether programs
satisfy their specifications or not, without having the actually run
the code! Dafny was developed by Rustan Leino at Microsoft Research,
one of the world's top research labs in computer science. It's also a
real revelation the first time one sees it alerting you to errors in
code without ever running it.
