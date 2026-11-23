# Open Problems

I want to list some problems that are small, but I think could lead to more interesting stuff, related to the dialectica constructions in my
phd thesis: "The Dialectica Categories", TR213 from Cambridge, https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf, 1991.
(the thesis was submitted in 1988, examined in Jan 1989, corrections accepted in 1990, published as a technical report in 1991)

Martin Hyland has some slides in https://www.dpmms.cam.ac.uk/~martin/Research/Slides/venice13.pdf about the relationship between type theory and dialectica.
(my own work has been on propositional and more recently first-order versions of the dialectica construction, 
the connections between polynomials happen for dependent types versions of Dialectica, the doctoral work of Moss 2018 and von Glehn 2016)

Sean Moss gave a very precise talk about it in the second Polynomials workshop:

https://www.youtube.com/watch?v=tw08TmO0RRo&t=7190s

https://topos.site/p-func-workshop/slides/Moss.pdf

but there is more to say about these connections, I believe.

*Status (2026):* my draft [Polynomials with Predicates: a Dialectica reading](https://github.com/vcvpaiva/Manuscripts/blob/main/DialPoly-7.pdf). not the whole story yet.

Dialectica categories exist in two shapes (Dial and Gir, the simplified form that has morphisms like Chu spaces).
They also exist both in subobject form or as maps into a lineale L. These variations should give us at least 4 types,
but I mostly discussed 2 of them: Dial with subobjects, Gir with a lineale.

1. Can we check that Dial with a lineale works too?

*Status (2026):*  Dial with a lineale is checked in the lab note [Dialectica categories without subobjects](https://github.com/vcvpaiva/Manuscripts/blob/main/DialWithoutSubobjects2.pdf); see also [Dialectica Constructions over Monoidal Bases](https://github.com/vcvpaiva/Manuscripts/blob/main/DialOverMonoidal.pdf) and [Dialectica over a Topos](https://github.com/vcvpaiva/Manuscripts/blob/main/DialOverTopos.pdf).

---

## A. Problems related to Lenses/Containers

Bruno Gavranovic talked about how Lenses and Optics differ operationally, see his website
https://www.brunogavranovic.com/

DBLP https://dblp.org/pid/245/2917.html

Intercat talk: https://www.youtube.com/watch?v=3NdYughK68Y

Bruno on machine learning and Optics
https://www.youtube.com/watch?v=1NHBexWYgkU

Bruno also produced a bibliography of what he thinks one should read if interested in lenses:
https://github.com/bgavran/Lens_Resources


2. question: Using the definition of lenses in Bruno's talk, it seems we could do a Dialectica Lens category, by adding a relation to Bruno's objects.
Would this be useful? if so, for which applications?

*Status (2026):* my draft [Bidirectional Transformations with Predicates](https://github.com/vcvpaiva/Manuscripts/blob/main/Lenses2026-8.pdf) adds relations to special kinds of lenses.

---

## B. Problems with Games

Jeremie Koenig gave a talk at ACT2021 which I thought was very insightful
https://www.youtube.com/watch?v=10u7hbEYcCk&t=3800s

slides: https://www.cl.cam.ac.uk/events/act2021/slides/ACT_2021_slides_71.pdf

his ACT paper: https://www.cl.cam.ac.uk/events/act2021/papers/ACT_2021_paper_71.pdf. 


Glynn Winskel gave a talk at the Topos Colloquium

https://www.youtube.com/watch?v=ywHNG6DYAGg 

his paper https://blogs.ed.ac.uk/he-lab/2022/03/14/new-paper-making-concurrency-functional/

My own super games preprint https://drive.google.com/file/d/19wSFHBNdb-PQj2ZjM6oZtV6MVutpGIdn/view?usp=sharing

*Status (2026):* my draft [Plays and Payoffs in Dialectica Games](https://github.com/vcvpaiva/Manuscripts/blob/main/GamesWithPayoffs-2.pdf).

---

## C. Implementations of Dialectica

Implementations can help us consolidate intuitions and also help us note where intuitions are a bit "shaky".

There is an implementation of Dialectica categories, coded in Agda by Harley Eades III, for the purpose of proving
cut-elimination for FILL (Full Intuitionistic Linear Logic). This is in https://github.com/heades/cut-fill-agda.
  (see https://github.com/bond15/Dialectica for a newer Cubical Agda version that is under development)

There is also an old implementation of Chu Spaces Live (in Java) at http://boole.stanford.edu/live/ which Vaughan Pratt maintains

Eric Bond has an implementation of polynomials here https://github.com/bond15/Polynomials-Categorically
and is implementing Dialectica categories here https://github.com/bond15/Dialectica.
My adaptation of his file is [DialSets.agda](DialSets.agda) in this repository.

The original Dialectica category was formalized in Lean's mathlib with Mario Carneiro in 2024:
https://github.com/leanprover-community/mathlib4/commit/5d74b273dd4c171c1f57a2d75abc1d3e27d7095a

It would be nice to have something calculating Dialectica spaces in CatLab, to improve synergy with J. Baez project.



