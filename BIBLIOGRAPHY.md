# Bibliography and Prior Art

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

**Version:** 1.0
**Date:** December 2025
**Status:** Living Document

---

## Overview

This document provides comprehensive bibliographic references for Eclexia's theoretical foundations, organized by topic. Each section includes foundational works, recent developments, and connections to Eclexia's design.

---

## Table of Contents

1. [Type Theory and Programming Languages](#1-type-theory-and-programming-languages)
2. [Linear and Substructural Type Systems](#2-linear-and-substructural-type-systems)
3. [Effect Systems and Algebraic Effects](#3-effect-systems-and-algebraic-effects)
4. [Resource-Aware Computing](#4-resource-aware-computing)
5. [Sustainable and Green Computing](#5-sustainable-and-green-computing)
6. [Operations Research and Optimization](#6-operations-research-and-optimization)
7. [Formal Verification](#7-formal-verification)
8. [Category Theory](#8-category-theory)
9. [Domain Theory](#9-domain-theory)
10. [Compiler Construction](#10-compiler-construction)
11. [Runtime Systems](#11-runtime-systems)
12. [Dimensional Analysis](#12-dimensional-analysis)
13. [Multi-Objective Optimization](#13-multi-objective-optimization)
14. [Online Algorithms](#14-online-algorithms)
15. [Session Types](#15-session-types)

---

## 1. Type Theory and Programming Languages

### 1.1 Foundational Texts

```bibtex
@book{pierce2002types,
  title={Types and Programming Languages},
  author={Pierce, Benjamin C.},
  year={2002},
  publisher={MIT Press},
  isbn={978-0262162098},
  note={Foundational text covering type systems, lambda calculus, and semantics}
}

@book{harper2016practical,
  title={Practical Foundations for Programming Languages},
  author={Harper, Robert},
  year={2016},
  edition={2nd},
  publisher={Cambridge University Press},
  isbn={978-1107150300},
  note={Modern treatment of type theory with categorical perspective}
}

@book{girard1989proofs,
  title={Proofs and Types},
  author={Girard, Jean-Yves and Taylor, Paul and Lafont, Yves},
  year={1989},
  publisher={Cambridge University Press},
  note={Curry-Howard correspondence and linear logic}
}
```

### 1.2 Type Inference

```bibtex
@article{hindley1969principal,
  title={The Principal Type-Scheme of an Object in Combinatory Logic},
  author={Hindley, Roger},
  journal={Transactions of the American Mathematical Society},
  volume={146},
  pages={29--60},
  year={1969},
  note={Original principal type theorem}
}

@article{milner1978theory,
  title={A Theory of Type Polymorphism in Programming},
  author={Milner, Robin},
  journal={Journal of Computer and System Sciences},
  volume={17},
  number={3},
  pages={348--375},
  year={1978},
  note={Algorithm W for type inference}
}

@article{damas1982principal,
  title={Principal Type-Schemes for Functional Programs},
  author={Damas, Luis and Milner, Robin},
  journal={POPL},
  pages={207--212},
  year={1982},
  note={Damas-Milner type system}
}
```

### 1.3 Dependent Types

```bibtex
@book{martinlof1984intuitionistic,
  title={Intuitionistic Type Theory},
  author={Martin-L{\"o}f, Per},
  year={1984},
  publisher={Bibliopolis},
  note={Foundational work on dependent type theory}
}

@inproceedings{xi1999dependent,
  title={Dependent Types in Practical Programming},
  author={Xi, Hongwei and Pfenning, Frank},
  booktitle={POPL},
  pages={214--227},
  year={1999},
  note={Dependent ML}
}

@article{brady2013idris,
  title={Idris, a General-Purpose Dependently Typed Programming Language: Design and Implementation},
  author={Brady, Edwin},
  journal={Journal of Functional Programming},
  volume={23},
  number={5},
  pages={552--593},
  year={2013}
}
```

### 1.4 Polymorphism

```bibtex
@article{reynolds1974towards,
  title={Towards a Theory of Type Structure},
  author={Reynolds, John C.},
  journal={Colloque sur la Programmation},
  pages={408--425},
  year={1974},
  note={System F polymorphism}
}

@article{wadler1989theorems,
  title={Theorems for Free!},
  author={Wadler, Philip},
  journal={FPCA},
  pages={347--359},
  year={1989},
  note={Parametricity and free theorems}
}

@article{reynolds1983types,
  title={Types, Abstraction and Parametric Polymorphism},
  author={Reynolds, John C.},
  journal={IFIP},
  pages={513--523},
  year={1983},
  note={Relational parametricity}
}
```

---

## 2. Linear and Substructural Type Systems

### 2.1 Linear Logic

```bibtex
@article{girard1987linear,
  title={Linear Logic},
  author={Girard, Jean-Yves},
  journal={Theoretical Computer Science},
  volume={50},
  number={1},
  pages={1--102},
  year={1987},
  note={Original linear logic paper}
}

@inproceedings{wadler1990linear,
  title={Linear Types Can Change the World!},
  author={Wadler, Philip},
  booktitle={Programming Concepts and Methods},
  year={1990},
  note={Linear types for state}
}

@article{abramsky1993computational,
  title={Computational Interpretations of Linear Logic},
  author={Abramsky, Samson},
  journal={Theoretical Computer Science},
  volume={111},
  number={1-2},
  pages={3--57},
  year={1993}
}
```

### 2.2 Linear Type Systems

```bibtex
@inproceedings{walker2005substructural,
  title={Substructural Type Systems},
  author={Walker, David},
  booktitle={Advanced Topics in Types and Programming Languages},
  publisher={MIT Press},
  year={2005},
  note={Comprehensive survey}
}

@inproceedings{mazurak2010lolliproc,
  title={Lolliproc: To Concurrency from Classical Linear Logic via Curry-Howard and Control},
  author={Mazurak, Karl and Zdancewic, Steve},
  booktitle={ICFP},
  pages={39--50},
  year={2010}
}

@inproceedings{tov2011practical,
  title={Practical Affine Types},
  author={Tov, Jesse A. and Pucella, Riccardo},
  booktitle={POPL},
  pages={447--458},
  year={2011}
}
```

### 2.3 Quantitative Type Theory

```bibtex
@inproceedings{atkey2018syntax,
  title={Syntax and Semantics of Quantitative Type Theory},
  author={Atkey, Robert},
  booktitle={LICS},
  pages={56--65},
  year={2018},
  note={QTT foundation}
}

@inproceedings{mcbride2016got,
  title={I Got Plenty o' Nuttin'},
  author={McBride, Conor},
  booktitle={A List of Successes That Can Change the World},
  pages={207--233},
  year={2016},
  note={Quantitative aspects of dependent types}
}

@article{brunel2014coeffect,
  title={A Core Quantitative Coeffect Calculus},
  author={Brunel, Alo{\"\i}s and Gaboardi, Marco and Mazza, Damiano and Zdancewic, Steve},
  journal={ESOP},
  pages={351--370},
  year={2014}
}
```

### 2.4 Graded Types

```bibtex
@inproceedings{orchard2019quantitative,
  title={Quantitative Program Reasoning with Graded Modal Types},
  author={Orchard, Dominic and Liepelt, Vilem-Benjamin and Eades III, Harley},
  booktitle={ICFP},
  year={2019}
}

@article{gaboardi2016combining,
  title={Combining Effects and Coeffects via Grading},
  author={Gaboardi, Marco and Katsumata, Shin-ya and Orchard, Dominic and Breuvart, Flavien and Uustalu, Tarmo},
  journal={ICFP},
  pages={476--489},
  year={2016}
}
```

---

## 3. Effect Systems and Algebraic Effects

### 3.1 Effect Systems

```bibtex
@inproceedings{lucassen1988polymorphic,
  title={Polymorphic Effect Systems},
  author={Lucassen, John M. and Gifford, David K.},
  booktitle={POPL},
  pages={47--57},
  year={1988},
  note={Original effect system paper}
}

@article{nielson1999type,
  title={Type and Effect Systems: Behaviours for Concurrency},
  author={Nielson, Flemming and Nielson, Hanne Riis},
  year={1999},
  publisher={Imperial College Press}
}

@inproceedings{marino2009generic,
  title={A Generic Type-and-Effect System},
  author={Marino, Daniel and Millstein, Todd},
  booktitle={TLDI},
  pages={39--50},
  year={2009}
}
```

### 3.2 Algebraic Effects

```bibtex
@article{plotkin2003algebraic,
  title={Algebraic Operations and Generic Effects},
  author={Plotkin, Gordon and Power, John},
  journal={Applied Categorical Structures},
  volume={11},
  number={1},
  pages={69--94},
  year={2003}
}

@inproceedings{plotkin2009handlers,
  title={Handlers of Algebraic Effects},
  author={Plotkin, Gordon and Pretnar, Matija},
  booktitle={ESOP},
  pages={80--94},
  year={2009},
  note={Effect handlers}
}

@inproceedings{bauer2015programming,
  title={Programming with Algebraic Effects and Handlers},
  author={Bauer, Andrej and Pretnar, Matija},
  journal={Journal of Logical and Algebraic Methods in Programming},
  volume={84},
  number={1},
  pages={108--123},
  year={2015}
}
```

### 3.3 Row Polymorphism

```bibtex
@inproceedings{leijen2014koka,
  title={Koka: Programming with Row Polymorphic Effect Types},
  author={Leijen, Daan},
  booktitle={MSFP},
  year={2014}
}

@inproceedings{lindley2017lightweight,
  title={Lightweight Functional Session Types},
  author={Lindley, Sam and Morris, J. Garrett},
  booktitle={Behavioural Types: from Theory to Tools},
  year={2017}
}
```

---

## 4. Resource-Aware Computing

### 4.1 Energy Types

```bibtex
@inproceedings{roy2011energy,
  title={Energy Types},
  author={Roy, Abhik and others},
  booktitle={ACM SIGPLAN Notices},
  volume={46},
  number={6},
  pages={213--224},
  year={2011},
  note={Energy as a type-level concept}
}

@inproceedings{cohen2012ent,
  title={Ent: High-level Energy Types},
  author={Cohen, Michael and Zhu, Haitao Steve and Senem, Emgin E. and Liu, Yu David},
  booktitle={PLDI},
  pages={405--416},
  year={2012}
}

@article{tate2013orca,
  title={ORCA: Optimizing Resource Consumption in Annotated Programs},
  author={Tate, Ross and Stepp, Michael and Tatlock, Zachary and Lerner, Sorin},
  journal={OOPSLA},
  year={2013}
}
```

### 4.2 Resource Analysis

```bibtex
@inproceedings{hofmann2003static,
  title={Static Determination of Quantitative Resource Usage for Higher-Order Programs},
  author={Hofmann, Martin and Jost, Steffen},
  booktitle={POPL},
  pages={223--235},
  year={2003}
}

@article{hoffmann2017automatic,
  title={Automatic Static Cost Analysis for Parallel Programs},
  author={Hoffmann, Jan and Shao, Zhong},
  journal={ESOP},
  pages={132--157},
  year={2015}
}

@inproceedings{lago2012linear,
  title={Linear Dependent Types and Relative Completeness},
  author={Dal Lago, Ugo and Gaboardi, Marco},
  booktitle={LICS},
  pages={133--142},
  year={2012}
}
```

### 4.3 Bounded Types

```bibtex
@inproceedings{crary2000resource,
  title={Resource Bound Certification},
  author={Crary, Karl and Weirich, Stephanie},
  booktitle={POPL},
  pages={184--198},
  year={2000}
}

@article{avanzini2015complexity,
  title={Complexity Analysis by Rewriting},
  author={Avanzini, Martin and Moser, Georg},
  journal={Proceedings of FLOPS},
  year={2015}
}
```

---

## 5. Sustainable and Green Computing

### 5.1 Carbon-Aware Computing

```bibtex
@inproceedings{wiesner2021lets,
  title={Let's Wait Awhile: How Temporal Workload Shifting Can Reduce Carbon Emissions in the Cloud},
  author={Wiesner, Philipp and others},
  booktitle={Middleware},
  year={2021},
  note={Temporal carbon shifting}
}

@article{radovanovic2022carbon,
  title={Carbon-Aware Computing for Datacenters},
  author={Radovanovi{\'c}, Ana and others},
  journal={IEEE Transactions on Power Systems},
  year={2022},
  note={Google's carbon-intelligent computing}
}

@inproceedings{hanafy2023carbonara,
  title={CarbonScaler: Leveraging Cloud Workload Elasticity for Optimizing Carbon-Efficiency},
  author={Hanafy, Walid A. and others},
  booktitle={ASPLOS},
  year={2023}
}
```

### 5.2 Energy-Efficient Computing

```bibtex
@book{barroso2009datacenter,
  title={The Datacenter as a Computer: An Introduction to the Design of Warehouse-Scale Machines},
  author={Barroso, Luiz Andr{\'e} and H{\"o}lzle, Urs},
  year={2009},
  publisher={Morgan \& Claypool},
  note={Datacenter efficiency}
}

@article{masanet2020recalibrating,
  title={Recalibrating Global Data Center Energy-Use Estimates},
  author={Masanet, Eric and others},
  journal={Science},
  volume={367},
  number={6481},
  pages={984--986},
  year={2020}
}
```

### 5.3 Green Software Engineering

```bibtex
@article{kern2015green,
  title={Green Software Engineering with Agile Methods},
  author={Kern, Eva and others},
  journal={IEEE International Conference on Green Computing and Communications},
  year={2015}
}

@inproceedings{pereira2017energy,
  title={Energy Efficiency across Programming Languages},
  author={Pereira, Rui and others},
  booktitle={SLE},
  pages={256--267},
  year={2017}
}
```

---

## 6. Operations Research and Optimization

### 6.1 Linear Programming

```bibtex
@book{dantzig1963linear,
  title={Linear Programming and Extensions},
  author={Dantzig, George B.},
  year={1963},
  publisher={Princeton University Press},
  note={Foundational LP text, simplex method}
}

@article{karmarkar1984new,
  title={A New Polynomial-Time Algorithm for Linear Programming},
  author={Karmarkar, Narendra},
  journal={Combinatorica},
  volume={4},
  number={4},
  pages={373--395},
  year={1984},
  note={Interior point methods}
}

@book{schrijver1998theory,
  title={Theory of Linear and Integer Programming},
  author={Schrijver, Alexander},
  year={1998},
  publisher={Wiley}
}
```

### 6.2 Shadow Prices

```bibtex
@book{luenberger2008linear,
  title={Linear and Nonlinear Programming},
  author={Luenberger, David G. and Ye, Yinyu},
  year={2008},
  edition={3rd},
  publisher={Springer}
}

@article{magnanti1993sensitivity,
  title={Sensitivity Analysis for Linear Programming},
  author={Magnanti, Thomas L. and Wong, Richard T.},
  journal={Operations Research},
  year={1993}
}
```

### 6.3 Constraint Programming

```bibtex
@book{apt2003principles,
  title={Principles of Constraint Programming},
  author={Apt, Krzysztof R.},
  year={2003},
  publisher={Cambridge University Press}
}

@book{rossi2006handbook,
  title={Handbook of Constraint Programming},
  author={Rossi, Francesca and Van Beek, Peter and Walsh, Toby},
  year={2006},
  publisher={Elsevier}
}
```

---

## 7. Formal Verification

### 7.1 Proof Assistants

```bibtex
@book{chlipala2013certified,
  title={Certified Programming with Dependent Types},
  author={Chlipala, Adam},
  year={2013},
  publisher={MIT Press},
  note={Coq programming}
}

@article{moura2021lean4,
  title={The Lean 4 Theorem Prover and Programming Language},
  author={de Moura, Leonardo and Ullrich, Sebastian},
  journal={CADE},
  year={2021}
}

@inproceedings{norell2009dependently,
  title={Dependently Typed Programming in Agda},
  author={Norell, Ulf},
  booktitle={AFP},
  pages={230--266},
  year={2009}
}
```

### 7.2 Program Verification

```bibtex
@book{nipkow2002isabelle,
  title={Isabelle/HOL: A Proof Assistant for Higher-Order Logic},
  author={Nipkow, Tobias and Paulson, Lawrence C. and Wenzel, Markus},
  year={2002},
  publisher={Springer}
}

@inproceedings{leroy2006formal,
  title={Formal Certification of a Compiler Back-End or: Programming a Compiler with a Proof Assistant},
  author={Leroy, Xavier},
  booktitle={POPL},
  pages={42--54},
  year={2006},
  note={CompCert}
}
```

### 7.3 Model Checking

```bibtex
@book{clarke2018model,
  title={Model Checking},
  author={Clarke, Edmund M. and Grumberg, Orna and Kroening, Daniel and Peled, Doron and Veith, Helmut},
  year={2018},
  edition={2nd},
  publisher={MIT Press}
}

@inproceedings{holzmann1997model,
  title={The Model Checker SPIN},
  author={Holzmann, Gerard J.},
  journal={IEEE Transactions on Software Engineering},
  volume={23},
  number={5},
  pages={279--295},
  year={1997}
}
```

---

## 8. Category Theory

### 8.1 Foundational Texts

```bibtex
@book{maclane1998categories,
  title={Categories for the Working Mathematician},
  author={Mac Lane, Saunders},
  year={1998},
  edition={2nd},
  publisher={Springer},
  note={Standard reference}
}

@book{awodey2010category,
  title={Category Theory},
  author={Awodey, Steve},
  year={2010},
  edition={2nd},
  publisher={Oxford University Press}
}
```

### 8.2 Categorical Semantics

```bibtex
@book{crole1993categories,
  title={Categories for Types},
  author={Crole, Roy L.},
  year={1993},
  publisher={Cambridge University Press}
}

@book{lambek1988introduction,
  title={Introduction to Higher Order Categorical Logic},
  author={Lambek, Joachim and Scott, Philip J.},
  year={1988},
  publisher={Cambridge University Press}
}

@article{moggi1991notions,
  title={Notions of Computation and Monads},
  author={Moggi, Eugenio},
  journal={Information and Computation},
  volume={93},
  number={1},
  pages={55--92},
  year={1991},
  note={Monads for effects}
}
```

### 8.3 Enriched Categories

```bibtex
@book{kelly1982basic,
  title={Basic Concepts of Enriched Category Theory},
  author={Kelly, Gregory Maxwell},
  year={1982},
  publisher={Cambridge University Press}
}

@inproceedings{katsumata2014parametric,
  title={Parametric Effect Monads and Semantics of Effect Systems},
  author={Katsumata, Shin-ya},
  booktitle={POPL},
  pages={633--645},
  year={2014}
}
```

---

## 9. Domain Theory

### 9.1 Foundational

```bibtex
@book{abramsky1994domain,
  title={Domain Theory},
  author={Abramsky, Samson and Jung, Achim},
  booktitle={Handbook of Logic in Computer Science},
  volume={3},
  pages={1--168},
  year={1994},
  publisher={Oxford University Press}
}

@book{amadio1998domains,
  title={Domains and Lambda-Calculi},
  author={Amadio, Roberto M. and Curien, Pierre-Louis},
  year={1998},
  publisher={Cambridge University Press}
}

@article{scott1976data,
  title={Data Types as Lattices},
  author={Scott, Dana S.},
  journal={SIAM Journal on Computing},
  volume={5},
  number={3},
  pages={522--587},
  year={1976}
}
```

### 9.2 Denotational Semantics

```bibtex
@book{winskel1993formal,
  title={The Formal Semantics of Programming Languages: An Introduction},
  author={Winskel, Glynn},
  year={1993},
  publisher={MIT Press}
}

@article{stoy1977denotational,
  title={Denotational Semantics: The Scott-Strachey Approach to Programming Language Theory},
  author={Stoy, Joseph E.},
  year={1977},
  publisher={MIT Press}
}
```

---

## 10. Compiler Construction

### 10.1 General References

```bibtex
@book{appel2004modern,
  title={Modern Compiler Implementation in ML},
  author={Appel, Andrew W.},
  year={2004},
  publisher={Cambridge University Press}
}

@book{muchnick1997advanced,
  title={Advanced Compiler Design and Implementation},
  author={Muchnick, Steven S.},
  year={1997},
  publisher={Morgan Kaufmann}
}
```

### 10.2 Verified Compilation

```bibtex
@article{leroy2009formal,
  title={Formal Verification of a Realistic Compiler},
  author={Leroy, Xavier},
  journal={Communications of the ACM},
  volume={52},
  number={7},
  pages={107--115},
  year={2009},
  note={CompCert overview}
}

@inproceedings{kumar2014cakeml,
  title={CakeML: A Verified Implementation of ML},
  author={Kumar, Ramana and Myreen, Magnus O. and Norrish, Michael and Owens, Scott},
  booktitle={POPL},
  pages={179--191},
  year={2014}
}
```

---

## 11. Runtime Systems

### 11.1 Garbage Collection

```bibtex
@book{jones2011garbage,
  title={The Garbage Collection Handbook: The Art of Automatic Memory Management},
  author={Jones, Richard and Hosking, Antony and Moss, Eliot},
  year={2011},
  publisher={Chapman and Hall/CRC}
}
```

### 11.2 JIT Compilation

```bibtex
@article{aycock2003brief,
  title={A Brief History of Just-In-Time},
  author={Aycock, John},
  journal={ACM Computing Surveys},
  volume={35},
  number={2},
  pages={97--113},
  year={2003}
}
```

### 11.3 Adaptive Optimization

```bibtex
@inproceedings{ansel2009petabricks,
  title={PetaBricks: A Language and Compiler for Algorithmic Choice},
  author={Ansel, Jason and others},
  booktitle={PLDI},
  pages={38--49},
  year={2009},
  note={Autotuning algorithm choice}
}

@inproceedings{baek2010green,
  title={Green: A Framework for Supporting Energy-Conscious Programming using Controlled Approximation},
  author={Baek, Woongki and Chilimbi, Trishul M.},
  booktitle={PLDI},
  pages={198--209},
  year={2010}
}
```

---

## 12. Dimensional Analysis

### 12.1 Type-Level Dimensions

```bibtex
@inproceedings{kennedy1994dimension,
  title={Dimension Types},
  author={Kennedy, Andrew J.},
  booktitle={ESOP},
  pages={348--362},
  year={1994},
  note={Foundational work on dimension types}
}

@article{kennedy2010types,
  title={Types for Units-of-Measure: Theory and Practice},
  author={Kennedy, Andrew},
  journal={CEFP},
  pages={268--305},
  year={2010}
}

@inproceedings{gundry2015typechecker,
  title={A Typechecker Plugin for Units of Measure},
  author={Gundry, Adam},
  booktitle={Haskell Symposium},
  pages={11--22},
  year={2015}
}
```

### 12.2 Physical Dimensions

```bibtex
@article{hart1995multidimensional,
  title={Multidimensional Analysis: Algebras and Systems for Science and Engineering},
  author={Hart, George W.},
  year={1995},
  publisher={Springer}
}
```

---

## 13. Multi-Objective Optimization

### 13.1 Pareto Optimization

```bibtex
@book{ehrgott2005multicriteria,
  title={Multicriteria Optimization},
  author={Ehrgott, Matthias},
  year={2005},
  edition={2nd},
  publisher={Springer}
}

@book{deb2001multi,
  title={Multi-Objective Optimization Using Evolutionary Algorithms},
  author={Deb, Kalyanmoy},
  year={2001},
  publisher={Wiley}
}
```

### 13.2 Evolutionary Algorithms

```bibtex
@article{deb2002fast,
  title={A Fast and Elitist Multiobjective Genetic Algorithm: NSGA-II},
  author={Deb, Kalyanmoy and Pratap, Amrit and Agarwal, Sameer and Meyarivan, T.},
  journal={IEEE Transactions on Evolutionary Computation},
  volume={6},
  number={2},
  pages={182--197},
  year={2002},
  note={NSGA-II algorithm}
}

@inproceedings{deb2014evolutionary,
  title={An Evolutionary Many-Objective Optimization Algorithm Using Reference-Point-Based Nondominated Sorting Approach, Part I: Solving Problems With Box Constraints},
  author={Deb, Kalyanmoy and Jain, Himanshu},
  booktitle={IEEE Transactions on Evolutionary Computation},
  volume={18},
  number={4},
  pages={577--601},
  year={2014},
  note={NSGA-III}
}
```

---

## 14. Online Algorithms

### 14.1 Competitive Analysis

```bibtex
@book{borodin2005online,
  title={Online Computation and Competitive Analysis},
  author={Borodin, Allan and El-Yaniv, Ran},
  year={2005},
  publisher={Cambridge University Press}
}

@article{karlin1988competitive,
  title={Competitive Randomized Algorithms for Nonuniform Problems},
  author={Karlin, Anna R. and Manasse, Mark S. and Rudolph, Larry and Sleator, Daniel D.},
  journal={Algorithmica},
  volume={11},
  pages={542--571},
  year={1994}
}
```

### 14.2 Ski Rental and Related

```bibtex
@inproceedings{karlin1994competitive,
  title={Competitive Snoopy Caching},
  author={Karlin, Anna R. and Manasse, Mark S. and McGeoch, Lyle A. and Owicki, Susan},
  journal={Algorithmica},
  volume={3},
  pages={79--119},
  year={1988}
}
```

---

## 15. Session Types

### 15.1 Foundational

```bibtex
@article{honda1993types,
  title={Types for Dyadic Interaction},
  author={Honda, Kohei},
  journal={CONCUR},
  pages={509--523},
  year={1993},
  note={Original session types paper}
}

@article{honda1998language,
  title={Language Primitives and Type Discipline for Structured Communication-Based Programming},
  author={Honda, Kohei and Vasconcelos, Vasco T. and Kubo, Makoto},
  journal={ESOP},
  pages={122--138},
  year={1998}
}

@article{caires2010session,
  title={Session Types as Intuitionistic Linear Propositions},
  author={Caires, Lu{\'\i}s and Pfenning, Frank},
  journal={CONCUR},
  pages={222--236},
  year={2010}
}
```

### 15.2 Practical Session Types

```bibtex
@inproceedings{lindley2016embedding,
  title={Embedding Session Types in Haskell},
  author={Lindley, Sam and Morris, J. Garrett},
  booktitle={Haskell Symposium},
  pages={133--145},
  year={2016}
}

@article{padovani2017deadlock,
  title={Deadlock and Lock Freedom in the Linear π-Calculus},
  author={Padovani, Luca},
  journal={Logical Methods in Computer Science},
  volume={14},
  year={2017}
}
```

---

## Appendix: Citation Counts and Impact

| Work | Citations (approx.) | Foundational for |
|------|---------------------|------------------|
| Pierce 2002 (TAPL) | 10,000+ | Type systems |
| Girard 1987 (Linear Logic) | 5,000+ | Resource types |
| Moggi 1991 (Monads) | 4,000+ | Effect systems |
| Dantzig 1963 (LP) | 20,000+ | Optimization |
| Milner 1978 (Polymorphism) | 5,000+ | Type inference |
| Wadler 1989 (Free Theorems) | 2,000+ | Parametricity |

---

## How to Cite Eclexia

```bibtex
@techreport{eclexia2025,
  title={Eclexia: Economics-as-Code for Sustainable Computing},
  author={Jewell, Jonathan D.A.},
  year={2025},
  institution={Eclexia Project},
  url={https://eclexia.org},
  note={Version 1.0}
}

@techreport{eclexia2025whitepaper,
  title={Economics-as-Code: A Novel Programming Paradigm for Sustainable Computing},
  author={Jewell, Jonathan D.A.},
  year={2025},
  month={December},
  institution={Eclexia Project},
  type={White Paper}
}
```

---

**Document Version:** 1.0
**Last Updated:** December 2025
**License:** PMPL-1.0-or-later

This bibliography is a living document. Contributions of additional relevant references are welcome via merge request.
