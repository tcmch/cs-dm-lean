This is a course, and a new kind of course, in discrete mathematics
(DM) for early undergaduate students in computer science and related
disciplines. The usual DM course at this level is a paper-and-pencil
affair about proof techniques many CS students find hard to relate to
their interests in computing.  This course charts a better way.

Several premises underlie the design of this course. First, students
want to know up front why logical proposition and proofs are relevant,
and how they are demonstrably and powerfully useful, for the practice
of computer science. This course thus grounds a study of mathematical
logic in the needs of software specification and verification. The
central idea is that while *code* is the language of implementation,
mathematical logic is the language of specification, and proofs, in
particular, are the language of verification.

Second, students of computer science are awed and inspired by *what
machines can do* when properly instructed. Moreover, recent, rapid,
and ongoing advances in the integration of logic and computing have
put us at the threshold of a new era in which every undergraduate
student of programming can and should be required to have a firm and
principled grounding in modern, *tool-supported* formal specification
and verification techniques.

A central premise of this course is this that students can now, should
now, and will be inspired to, see how mathematical logic and proof can
be applied, automated, and used for mechanical checking of code using
modern program verification tools.

The limited aim of the first segment of this course is to familiarize
students with the language and uses of first-order predicate logic by
teaching them how to write pre-/post-condition specifications, logical
assertions, and loop invariants for code that can then be verified by
a tool. The first part of the course thus relieves them of the need to
understand proofs. This course thus teaches imperative and functional
programming and specification using Dafny, and uses Dafny's SMT-based
program verification engine to provide students immediate feedback on
their specifications and programs.

Third, the effective study of set theory, relational logic, order
theory, and related concepts relies on a reasonable degree of fluency
in first-order predicate logic. The study of these topics should thus
occur only after students have hadsome significant practice with the
language of predicate logic. That said, studying set theory and its
related concepts will provide significant additional practice with and
will deepen students' understanding of this language and its uses.

Furthermore, while the set and relational abstraction provided by most
industrial programming languages are conceptually compromised (what on
earth is a *hashmap*, for example), the libraries of carefully defined
modern verifications systems are almost idea for teaching *automated*
set theory. Dafny's finite *set* and infinite *iset* types provide
operations and notations that directly reflect the corresponding set
theory, for example. One write cardinalities, unions, comprehensions,
etc. with very natural syntax and semantics. Rather than learning set
theory as an arcane paper-and-pencil exercise, students can now learn
it by writing beautiful code that they can play with and run.

Third, the on-ramp to learning proof techniques is complex and should
be taught through a step-by-step development of underlying principles.
This course therefore takes students on an incremental journey through
an evolving landscape of deepening concepts. Having developed students'
fluency in reading, writing, and *benefitting from* predicate logic, the
course then asks and starts to answer the question, *what is a logic*?

This question leads directly to the notion of a formal language, which
the course then addresses in the style of modern type theory. As an
easy warm-up, students learn how to specify the *syntax* of a simple
variant of the language of Boolean expressions (with both literals and
connectives but no variables) using *inductive type definitions*; and
they learn how to specify and implement the *semantics* of a language
using *pattern matching* and *structural recursion* over terms of the
language.

In the next chapter, students first extend this language to support
Boolean variables, leading to the core concept of an environment or
interpretation: or to a *state* in which an expression that includes
variables is evaluated. From there it's a simple observation that the
students have constructed a language fully isomorphic to propositional
logic!

The concepts of models and of satisfiability (there exists a model),
of validity (for all models), and of unsatisfiability (there does not
exist a model) all follow directly. The class works through a basic
implementation of a SAT solver and validity/unsatisfiability checker
using truth tables.


Next, leveraging the same code base, students work through the concept
and implementation of *named inference rules* for *natural deduction*
for propositional logic, using our validity checker to test whether
proposed *reasoning principles* (inference rules) are valid or not.
They are thus led to the concept of *semantic entailment*. The also
see that it cannot scale because truth tables are exponential in the
number of variables in a given proposition. Incidentally, the coding
of these capabilities provides students with more and deeper examples
of the uses of specifications to write and check clean, correct code.

Finally, students are led to the notions of *syntactic entailment*,
and thus of *derivations* and *proofs*. At this point, the course
finally "surfaces" proof objects, and does so by changing tools from
Dafny to Lean, a new constructive logic proof assistant that, like
Dafny, was (and continues to be) developed at Microsoft Research (by
Leo de Moura). The introduction and elimination rules of natural
deduction are now recapitulated, but now in the context and language
of higher-order constructive logic.

From there, proof strategies are taught as following in many cases
from the form of the proposition to be proved. Rather than initially
learning proofs as informal paper-and-pencil constructions, they see
them as precisely and inductively formed objects. The powerful type
system of Lean, which includes typed *holes* provides very beautiful
support for top-down structured development of proof objects, and,
indeed of programs, since programs are, of course, ultimately, also
proofs: of their types.

Chapters follow on proof techniques deriving from the various forms of
propositions, ultimately reaching proofs by induction for universally
quantified propositions. (Notes not yet in place: TBD).

The course used the Dafny and Lean languages, and used VS Code and the
Dafny and Lean extensions for VS Code for all student work. The Dafny
and Lean languages cased few complications. The VS Code extensions
still need some work. Both the Dafny and Lean extensions sometimes
fail to properly update error indications (red squiggly underlines),
even when code is correct, which generally and understandably causes
great consternation, frustration, anger, and sadness among early CS
students, until they learn the work-arounds. Instructors considering
using this curriculum should be aware of these issues. The author is
happy to discuss them with other instructors and investigators who
might be interested.

Exercises are currently provided in some but not all chapters. This is
work that planned for completion by the start of Fall semester, 2018.


.. todo

   Add missing chapters

The design of this course owes a lot to many other researchers. It was
inspired by pedagogical works organized around Coq, notably Benjamin
Pierce's Software Foundations and Chlipala's Certified Programming
with Dependent Types. Unlike those works, this course is geared to the
beginning undergraduate students in computer science, and so it aims
to make no assumptions about prior knowledge except of the most
fundamental constructs of imperative programming.

This course was also inspired and influenced by the *How to Design
Programs* curricula by Felleisen, Krishnamurthi, et al., and realized
perhaps most fully in the *MOOC* courses by Kiczales at UBC.  Unlike
those courses, however, this one take a strong stand on the absolute
necessity of using strongly typed languages. The HTDP's basis in the
untyped language of Scheme (Racket) leaves the type-driven ideas that
underpin the curriculum unsupported by the language and tools that the
students actually use to learn programming. This course necessarily
makes an absolyte commitment to the *pedagogical* value of strong
typing, as enforced by Dafny, and as realized in the Lean language's
full embrace of higher-order constructive logic and the Curry-Howard
correspondence.

The author gratefully acknowledges the support of Rustan Leino, the
developer of Dafny, and several others who provided insight and help
in the author's use of Dafny; of Leo de Moura, Tom Ball, and Jeremy
Avigad for their help with Lean (and Jeremy for open source code that
taught the author how to format this book using Sphinx); of Mattias
Felleisen, Shriram Krishnamurthi, Gregor Kiczales, and others for many
discussions about HTDP and related pedagogical strategies; and Ken
Birman, who suggested that the author look at Dafny as a strong
candidate for a first or early course for computer scientists. The
author also thanks the students in his CS2102 Spring 2018 class for
their patience and enthusiasm for learning discrete math following
this somewhat novel approach to teaching that class. Thanks y'all.


