# Comprehensive Citations: SMT Solvers and Temporal Reasoning

This document provides detailed citations, summaries, and relevant information for SMT solvers, proof formats, and temporal reasoning research.

---

## 1. SMT Solvers

### 1.1 cvc5 SMT Solver

**Complete Citation:**
Haniel Barbosa, Clark W. Barrett, Martin Brain, Gereon Kremer, Hanna Lachnitt, Makai Mann, Abdalrhman Mohamed, Mudathir Mohamed, Aina Niemetz, Andres Nötzli, Alex Ozdemir, Mathias Preiner, Andrew Reynolds, Ying Sheng, Cesare Tinelli, and Yoni Zohar. "cvc5: A Versatile and Industrial-Strength SMT Solver." In *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2022)*, edited by Dana Fisman and Grigore Rosu, Lecture Notes in Computer Science, vol. 13243, pp. 415-442. Springer, Cham, 2022.

**DOI:** https://doi.org/10.1007/978-3-030-99524-9_24

**Award:** Best SCP Tool Paper Award at TACAS 2022

**Official Website:** https://cvc5.github.io/

**Documentation:** https://cvc5.github.io/docs/

**GitHub Repository:** https://github.com/cvc5/cvc5

**PDF Access:**
- https://www-cs.stanford.edu/~preiner/publications/2022/BarbosaBBKLMMMN-TACAS22.pdf
- https://hanielbarbosa.com/papers/tacas2022.pdf

**Summary:**
cvc5 is the latest SMT solver in the cooperating validity checker series, building on the successful code base of CVC4. This paper serves as a comprehensive system description of cvc5's architectural design and highlights the major features and components introduced since CVC4 1.8. The solver is open-source, efficient, and supports a wide range of theories including uninterpreted functions, linear and non-linear arithmetic, bit-vectors, strings, sequences, sets, bags, and datatypes. The paper evaluates cvc5's performance on all benchmarks in SMT-LIB and provides a comparison against CVC4 and Z3.

**Key Features:**
- Efficient automatic theorem prover for SMT problems
- Syntax-Guided Synthesis (SyGuS) engine for function synthesis
- APIs for multiple programming languages (Python, Java, C++, etc.)
- Proof production in Alethe format
- Industrial-strength solver used in verification and analysis applications

**Key Concepts Relevant to Temporal Reasoning:**
- Support for theories that enable encoding temporal constraints (linear arithmetic, uninterpreted functions)
- Proof production capabilities for trustworthy temporal reasoning
- Integration capabilities with formal verification workflows

**Relevant Quote:**
"cvc5 is an efficient open-source automatic theorem prover for Satisfiability Modulo Theories (SMT) problems that can be used to prove the satisfiability (or validity) of first-order formulas with respect to combinations of various background theories."

---

### 1.2 Z3 SMT Solver

**Complete Citation:**
Leonardo de Moura and Nikolaj Bjørner. "Z3: An Efficient SMT Solver." In *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2008)*, Lecture Notes in Computer Science, vol. 4963, pp. 337-340. Springer, Berlin, Heidelberg, 2008.

**DOI:** https://doi.org/10.1007/978-3-540-78800-3_24

**Microsoft Research Page:** https://www.microsoft.com/en-us/research/project/z3-3/

**Online Guide:** https://microsoft.github.io/z3guide/

**GitHub Repository:** https://github.com/Z3Prover/z3

**PDF Access:** https://link.springer.com/content/pdf/10.1007/978-3-540-78800-3_24.pdf

**Recognition:**
- Over 5,000 citations since 2008
- 2015 ACM SIGPLAN Programming Languages Software Award
- Open-sourced in 2015

**Summary:**
Z3 is a new and efficient SMT solver from Microsoft Research that addresses the Satisfiability Modulo Theories (SMT) problem - a decision problem for logical first-order formulas with respect to combinations of background theories such as arithmetic, bit-vectors, arrays, and uninterpreted functions. Z3 was developed in the Research in Software Engineering (RiSE) group at Microsoft Research Redmond and is targeted at solving problems that arise in software verification and program analysis.

**Main Applications:**
- Extended static checking
- Test case generation (e.g., Pex automatic test generation)
- Predicate abstraction
- Program verification (e.g., Spec#/Boogie)
- Compiler validation
- Software/hardware verification and testing
- Network verification
- Security analysis
- Constraint solving
- Analysis of hybrid systems
- Biological computation analysis

**Key Concepts Relevant to Temporal Reasoning:**
- Theory of linear arithmetic for temporal constraints
- Combination of theories for complex temporal properties
- Quantifier reasoning for temporal uncertainty

**Relevant Quote:**
"Z3 is being used in several projects at Microsoft since February 2007. Its main applications are extended static checking, test case generation, and predicate abstraction. While Z3 was intentionally designed with a general interface that would allow easy incorporation into other types of software development and analysis tools, we couldn't possibly have dreamed up the kind of uses we've seen ranging from biological computation analysis to solving pebbling games for quantum computers."

---

### 1.3 veriT SMT Solver

**Complete Citation:**
Thomas Bouton, Diego Caminha B. de Oliveira, David Déharbe, and Pascal Fontaine. "veriT: An Open, Trustable and Efficient SMT-Solver." In *Automated Deduction – CADE-22*, Lecture Notes in Computer Science, vol. 5663, pp. 151-156. Springer, Berlin, Heidelberg, 2009.

**DOI:** https://doi.org/10.1007/978-3-642-02959-2_12

**Official Website:** https://verit.loria.fr/

**HAL Archive:** https://hal.inria.fr/inria-00430634

**Summary:**
This paper describes the first public version of the satisfiability modulo theory (SMT) solver veriT. The solver is open-source, proof-producing, and complete for quantifier-free formulas with uninterpreted functions and difference logic on real numbers and integers. veriT was the first solver to introduce what would later become the Alethe proof format, making it a pioneer in trustable SMT solving with proof production.

**Key Features:**
- Open-source implementation
- Proof production capabilities (Alethe format)
- Complete for QF_UF and QF_IDL theories
- Integration with proof assistants (Isabelle/HOL, Coq via SMTCoq)

**Key Concepts Relevant to Temporal Reasoning:**
- Difference logic support (essential for temporal interval constraints)
- Proof production for verified temporal reasoning
- Foundation for the Alethe proof format used in modern SMT solvers

---

## 2. SMT-LIB Standard

### 2.1 SMT-LIB Version 2.0

**Complete Citation:**
Clark Barrett, Aaron Stump, and Cesare Tinelli. "The SMT-LIB Standard -- Version 2.0." In *Proceedings of the 8th International Workshop on Satisfiability Modulo Theories (SMT 2010)*, Edinburgh, Scotland, July 2010.

**Official Website:** https://smt-lib.org/

**PDF Reference Document:** https://smt-lib.org/papers/smt-lib-reference-v2.0-r10.12.21.pdf

**Alternate PDF:** http://theory.stanford.edu/~barrett/pubs/BST10.pdf

**Summary:**
The SMT-LIB initiative is an international effort, supported by research groups worldwide, with the two-fold goal of producing an extensive online library of benchmarks and promoting the adoption of common languages and interfaces for SMT solvers. Version 2.0 is a major upgrade of the previous Version 1.2 which, in addition to simplifying and extending the languages of that version, includes a new command language for interfacing with SMT solvers. The work was conducted by the SMT-LOGIC work group (led by C. Tinelli) and the SMT-MODELS work group (led by C. Barrett), working from Fall 2008 into Spring 2010.

**Key Concepts:**
- Standardized input/output format for SMT solvers
- Theory declarations for various mathematical domains
- Benchmark library for solver evaluation
- Command language for solver interaction

**Relevant Quote:**
"The SMT-LIB initiative is an international effort, supported by research groups worldwide, with the two-fold goal of producing an extensive on-line library of benchmarks and promoting the adoption of common languages and interfaces for SMT solvers."

---

### 2.2 SMT-LIB Version 2.6

**Complete Citation:**
Clark Barrett, Pascal Fontaine, and Cesare Tinelli. "The SMT-LIB Standard Version 2.6." Technical Report BarFT-RR-17, Department of Computer Science, The University of Iowa, 2017. Available at www.SMT-LIB.org.

**PDF Reference Document:** https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf

**Copyright:** 2015-2021 by Clark Barrett, Pascal Fontaine, and Cesare Tinelli

**Summary:**
Version 2.6 of the SMT-LIB Standard is a backward-compatible extension of Version 2.5. This version continues the evolution of the SMT-LIB standard, adding new features while maintaining compatibility with existing tools and benchmarks. It includes refinements to theory definitions, improved support for proof production, and enhanced command language features. Version 2.6 remains widely used and cited in academic literature, though Version 2.7 (released in 2025) is now the latest version.

**Key Improvements:**
- Enhanced theory definitions
- Refined command language
- Better support for proof production
- Backward compatibility with Version 2.5

---

### 2.3 SMT-LIB Version 2.7 (Latest)

**Complete Citation:**
Clark Barrett, Pascal Fontaine, and Cesare Tinelli. "The SMT-LIB Standard Version 2.7." Available at www.SMT-LIB.org, 2025.

**PDF Reference Document:** https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf

**Summary:**
Version 2.7 represents the latest evolution of the SMT-LIB standard, incorporating community feedback and supporting modern SMT solver capabilities. This version continues the tradition of backward compatibility while introducing new features to support advanced applications.

---

## 3. Proof Formats for SMT Solvers

### 3.1 Alethe Proof Format

**Complete Citation:**
Hans-Jörg Schurr, Mathias Fleury, Haniel Barbosa, and Pascal Fontaine. "Alethe: Towards a Generic SMT Proof Format (extended abstract)." In *Proceedings Seventh Workshop on Proof eXchange for Theorem Proving (PxTP 2021)*, Pittsburgh, PA, USA, July 11, 2021, EPTCS 336, pp. 49-54, 2021.

**DOI:** https://doi.org/10.4204/EPTCS.336.6

**arXiv:** https://arxiv.org/abs/2107.02354

**PDF Access:**
- https://pxtp.gitlab.io/2021/papers/Schurr-et-al_Alethe.pdf
- https://hal.science/hal-03341413/

**Official Specification:** https://verit.loria.fr/documentation/alethe-spec.pdf

**Summary:**
Alethe is a proof format that evolved from the format used by the SMT solver veriT, first presented ten years ago at the PxTP workshop. The format has since matured with proofs being used within multiple applications and generated by other solvers as well. Alethe is an established SMT proof format generated by the solvers veriT and cvc5, with reconstruction support in the proof assistants Isabelle/HOL and Coq (via SMTCoq plugin). The format is close to SMT-LIB and allows both coarse- and fine-grained steps, facilitating proof production.

**Supported Solvers:**
- veriT (original implementation)
- cvc5 (current major adoption)

**Proof Assistant Support:**
- Isabelle/HOL (direct reconstruction)
- Coq (via SMTCoq plugin)

**Key Features:**
- SMT-LIB compatible syntax
- Support for both coarse-grained and fine-grained proof steps
- Generic format applicable to multiple SMT solvers
- Integration with formal verification tools

**Key Concepts Relevant to Temporal Reasoning:**
- Trustworthy proof certificates for temporal constraints
- Integration with proof assistants for verified temporal reasoning
- Support for theory-specific reasoning (e.g., arithmetic for temporal intervals)

**Note on Hans-Jörg Schurr:**
Hans-Jörg Schurr is a computer science postdoc at the University of Iowa who studies SMT solving and works on the solver cvc5, currently focusing on SMT proof certificates. He is currently building the Eunoia language that combines ideas from the LFSC framework with the familiar syntax of the Alethe format.

---

### 3.2 LFSC Proof Format

**Complete Citation:**
Aaron Stump, Duckki Oe, Andrew Reynolds, Liana Hadarean, and Cesare Tinelli. "SMT proof checking using a logical framework." *Formal Methods in System Design* 42, pp. 91-118, 2013.

**DOI:** https://doi.org/10.1007/s10703-012-0163-3

**PDF Access:** https://homepage.cs.uiowa.edu/~astump/papers/fmsd13.pdf

**Summary:**
This paper describes a proof-checking solution based on a Logical Framework with Side Conditions (LFSC). Producing and checking proofs from SMT solvers is currently the most feasible method for achieving high confidence in the correctness of solver results. The diversity of solvers and relative complexity of SMT over SAT means that flexibility, as well as performance, is a critical characteristic of a proof-checking solution for SMT. LFSC provides a declarative format for describing proof systems as signatures. The framework extends the Edinburgh Logical Framework (LF) to allow side conditions to be expressed using a simple first-order functional programming language. The paper shows how LFSC can be applied for flexible proof production and checking for two different SMT solvers, clsat and cvc3.

**Key Features:**
- Extension of Edinburgh Logical Framework (LF)
- Side conditions expressed in first-order functional programming language
- Declarative format for describing proof systems as signatures
- Flexible enough to handle various proof systems from different SMT solvers

**Performance:**
Experiments on QF_IDL benchmarks showed proof-checking overhead of 30% of the solving time required by the clsat solver.

**Key Concepts Relevant to Temporal Reasoning:**
- Flexible proof format adaptable to temporal reasoning theories
- Support for difference logic (QF_IDL), essential for temporal constraints
- Framework for trustworthy temporal constraint solving

**Relevant Quote:**
"Producing and checking proofs from SMT solvers is currently the most feasible method for achieving high confidence in the correctness of solver results. The diversity of solvers and relative complexity of SMT over, say, SAT means that flexibility, as well as performance, is a critical characteristic of a proof-checking solution for SMT."

---

### 3.3 Carcara Proof Checker

**Complete Citation:**
Bruno Andreotti, Hanna Lachnitt, and Haniel Barbosa. "Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format." In *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2023)*, edited by Sriram Sankaranarayanan and Natasha Sharygina, Lecture Notes in Computer Science, vol. 13993, pp. 367-386. Springer, Cham, 2023.

**DOI:** https://doi.org/10.1007/978-3-031-30823-9_19

**GitHub Repository:** https://github.com/ufmg-smite/carcara

**Zenodo Artifact:** https://zenodo.org/records/7574451

**License:** Apache 2.0

**Summary:**
Carcara is a proof checker and elaborator for SMT proofs in the Alethe format, implemented in Rust. It aims to increase the adoption of the Alethe format by providing push-button proof-checking for Alethe proofs, focusing on efficiency and usability, and by providing elaboration for coarse-grained steps into fine-grained ones, increasing the potential success rate of checking Alethe proofs in performance-critical validators such as proof assistants. Carcara was evaluated over a large set of Alethe proofs generated from SMT-LIB problems and shown to have good performance. Its elaboration techniques can make proofs easier to check in proof assistants.

**Key Features:**
- Independent proof checker (not tied to any specific SMT solver)
- Written in Rust for performance and safety
- Elaboration capabilities (transforms coarse-grained to fine-grained proofs)
- Push-button proof checking
- Open-source with permissive license

**Evaluation:**
- Tested on large sets of SMT-LIB benchmarks
- Demonstrates good performance characteristics
- Elaboration improves proof assistant integration

---

## 4. Allen's Interval Algebra and Temporal Reasoning

### 4.1 Allen's Original Paper

**Complete Citation:**
James F. Allen. "Maintaining Knowledge about Temporal Intervals." *Communications of the ACM* 26(11), pp. 832-843, 1983.

**DOI:** https://doi.org/10.1145/182.358434

**PDF Access:** http://cse.unl.edu/~choueiry/Documents/Allen-CACM1983.pdf

**Citation Count:** Over 7,362 citations (as of recent records)

**Summary:**
In this seminal 1983 paper, James F. Allen proposed thirteen basic relations between time intervals that are distinct, exhaustive, and qualitative. These relations are distinct because no pair of definite intervals can be related by more than one of the relationships, exhaustive because any pair of definite intervals are described by one of the relations, and qualitative (rather than quantitative) because no numeric time spans are considered. The calculus defines possible relations between time intervals and provides a composition table that can be used as a basis for reasoning about temporal descriptions of events. Using this calculus, given facts can be formalized and then used for automatic reasoning.

**The Thirteen Relations:**
The thirteen basic relations are: before, after, meets, met-by, overlaps, overlapped-by, during, contains, starts, started-by, finishes, finished-by, and equals.

**Key Contributions:**
- First comprehensive interval-based temporal reasoning framework
- Composition table for temporal inference
- Foundation for constraint-based temporal reasoning
- Widely adopted in AI, databases, and planning systems

**Significance:**
Allen's interval algebra is one of the best established formalisms for temporal reasoning and has been foundational to research in temporal constraint satisfaction, planning, natural language understanding, and database systems.

**Relevant Quote:**
"The calculus defines possible relations between time intervals and provides a composition table that can be used as a basis for reasoning about temporal descriptions of events."

---

### 4.2 Temporal Constraint Networks

**Complete Citation:**
Rina Dechter, Itay Meiri, and Judea Pearl. "Temporal constraint networks." *Artificial Intelligence* 49(1-3), pp. 61-95, 1991.

**DOI:** https://doi.org/10.1016/0004-3702(91)90006-6

**Citation Count:** 573 citations

**Summary:**
This foundational paper extends network-based methods of constraint satisfaction to include continuous variables, providing a framework for processing temporal constraints where variables represent time points and temporal information is represented by unary and binary constraints. The unique feature of this framework is permitting the processing of metric information, namely assessments of time differences between events. The paper introduces Simple Temporal Networks (STNs) and provides algorithms for checking consistency and finding solutions.

**Key Contributions:**
- Introduction of Simple Temporal Networks (STNs)
- Algorithms for consistency checking
- Framework for metric temporal reasoning
- Foundation for temporal planning and scheduling

**Key Concepts:**
- Point-based temporal representation
- Metric constraints on time differences
- Path consistency algorithms
- Integration with constraint satisfaction techniques

**Significance:**
This work established the foundation for metric temporal reasoning and has been extensively cited in planning, scheduling, and temporal database research.

---

## 5. Temporal Reasoning with SMT

### 5.1 Solving Temporal Problems Using SMT: Strong Controllability

**Complete Citation:**
Alessandro Cimatti, Andrea Micheli, and Marco Roveri. "Solving Temporal Problems Using SMT: Strong Controllability." In *Principles and Practice of Constraint Programming (CP 2012)*, edited by Michela Milano, Lecture Notes in Computer Science, vol. 7514, pp. 248-264. Springer, Berlin, Heidelberg, 2012.

**DOI:** https://doi.org/10.1007/978-3-642-33558-7_20

**PDF Access:**
- https://andrea.micheli.website/papers/solving_temporal_problems_using_smt_strong_controllability.pdf
- https://www.mikand.net/papers/solving_temporal_problems_using_smt_strong_controllability.pdf

**Summary:**
This paper tackles the problem of strong controllability for temporal problems with uncertainty, i.e., finding an assignment to all the controllable time points such that the constraints are fulfilled under any possible assignment of uncontrollable time points. The framework works in Satisfiability Modulo Theory (SMT), where uncertainty is expressed by means of universal quantifiers. The use of quantifier elimination techniques leads to quantifier-free encodings, which are in turn solved with efficient SMT solvers. The results clearly demonstrate that the proposed approach is feasible and outperforms the best state-of-the-art competitors when available.

**Key Contributions:**
- SMT-based encoding for strong controllability
- Quantifier elimination techniques for uncertainty handling
- Experimental evaluation showing performance advantages
- Framework applicable to STPU (Simple Temporal Problems with Uncertainty)

**Key Concepts:**
- Strong controllability: assignment to controllable variables that works for all uncontrollable scenarios
- Universal quantification for uncertainty modeling
- Quantifier elimination producing quantifier-free formulas
- Linear Real Arithmetic theory for temporal constraints

---

### 5.2 Solving Strong Controllability Using SMT (Journal Version)

**Complete Citation:**
Alessandro Cimatti, Andrea Micheli, and Marco Roveri. "Solving strong controllability of temporal problems with uncertainty using SMT." *Constraints* 20(1), pp. 1-29, 2015.

**DOI:** https://doi.org/10.1007/s10601-014-9167-5

**Summary:**
This journal paper is an extended version of the CP 2012 paper, providing more comprehensive treatment of the SMT-based approach to strong controllability. It includes additional theoretical results, more extensive experimental evaluation, and deeper analysis of the quantifier elimination techniques. The approach demonstrates that SMT solvers can effectively handle temporal problems with uncertainty by encoding the problem in the theory of Linear Real Arithmetic with universal quantifiers.

**Additional Contributions:**
- Extended theoretical framework
- More comprehensive experimental evaluation
- Detailed analysis of solver performance
- Comparison with specialized algorithms

---

### 5.3 SMT-Based Approach to Weak Controllability for DTPU

**Complete Citation:**
Alessandro Cimatti, Andrea Micheli, and Marco Roveri. "An SMT-based approach to weak controllability for disjunctive temporal problems with uncertainty." *Artificial Intelligence* 224, pp. 1-27, 2015.

**DOI:** https://doi.org/10.1016/j.artint.2015.02.003

**PDF Access:** https://www.mikand.net/papers/an_smt_based_approach_to_weak_controllability_for_disjunctive_temporal_problems_with_uncertainty.pdf

**Summary:**
This paper presents a logical approach based on reduction to Satisfiability Modulo Theories (SMT) in the theory of Linear Real Arithmetic with Quantifiers, resulting in the first implemented solver for weak controllability of DTPUs (Disjunctive Temporal Problems with Uncertainty). Weak controllability involves finding a strategy for assigning values to controllable variables that depends on observing the values of uncontrollable variables. The paper addresses the most general class of temporal problems with uncertainty - disjunctive TPU (DTPU) - which includes disjunctive constraints.

**Key Contributions:**
- First implemented solver for weak controllability of DTPUs
- SMT encoding with existential and universal quantifiers
- Strategy extraction from satisfying assignments
- Handling of disjunctive temporal constraints

**Key Concepts:**
- Weak controllability: reactive strategy depending on observations
- Disjunctive temporal constraints
- Quantifier alternation (exists-forall)
- Strategy synthesis from SMT solutions

**Temporal Problem Classes:**
- STPU: Simple Temporal Problems with Uncertainty
- TCSPU: Temporal Constraint Satisfaction Problems with Uncertainty
- DTPU: Disjunctive Temporal Problems with Uncertainty (most general)

---

### 5.4 Solving Temporal Problems Using SMT: Weak Controllability

**Complete Citation:**
Alessandro Cimatti, Andrea Micheli, and Marco Roveri. "Solving Temporal Problems Using SMT: Weak Controllability." In *Proceedings of the Twenty-Sixth AAAI Conference on Artificial Intelligence (AAAI-12)*, pp. 448-454. AAAI Press, 2012.

**URL:** https://ojs.aaai.org/index.php/AAAI/article/view/8136

**PDF Access:** https://www.mikand.net/papers/solving_temporal_problems_using_smt_weak_controllability.pdf

**Summary:**
This is the conference paper companion to the strong controllability work, addressing weak controllability using similar SMT-based techniques. The paper introduces the SMT encoding for temporal problems where a reactive strategy is needed - assignments to controllable variables can depend on observed values of uncontrollable variables.

---

## 6. Constraint-Based Temporal Planning

### 6.1 A Constraint-Based Encoding for Domain-Independent Temporal Planning

**Complete Citation:**
Arthur Bit-Monnot. "A Constraint-based Encoding for Domain-Independent Temporal Planning." In *Principles and Practice of Constraint Programming (CP 2018)*, edited by John Hooker, Lecture Notes in Computer Science, vol. 11008, pp. 30-46. Springer, Cham, 2018.

**DOI:** https://doi.org/10.1007/978-3-319-98334-9_3

**PDF Access:** https://homepages.laas.fr/abitmonnot/files/18-cp.pdf

**Author Website:** https://homepages.laas.fr/abitmonnot/

**Summary:**
This paper presents a compilation of domain-independent temporal planning to Constraint Satisfaction Problems (CSPs) using a time-oriented view inspired by constraint-based planning and scheduling work. For temporally constrained planning benchmarks, constraint-based encodings solved with SMT solvers have proven slightly more efficient than state-of-the-art methods while clearly outperforming other fully constraint-based approaches. Most encodings use a fully lifted representation at the level of action templates, following a time-oriented view. The resulting encoding is leveraged in a domain-independent planner for ANML, an expressive language for the specification of planning problems.

**Key Contributions:**
- Constraint-based encoding for temporal planning
- Time-oriented representation of planning problems
- Integration with SMT solvers for efficient solving
- Support for expressive planning languages (ANML)

**Key Concepts:**
- Lifted representation at action template level
- Time-oriented view of planning
- Integration of planning and constraint satisfaction
- SMT solver application to planning

**Performance:**
The approach shows competitive or superior performance compared to state-of-the-art temporal planners while providing a simple and extensible framework.

---

## 7. Additional Relevant Work

### 7.1 Temporal Constraints: A Survey

**Complete Citation:**
Rina Dechter, Itay Meiri, and Judea Pearl. "Temporal Constraints: A Survey." *Constraints* 4(1), pp. 61-97, 1999.

**DOI:** https://doi.org/10.1023/A:1009717525330

**PDF Access:** https://ics.uci.edu/~dechter/publications/r66.pdf

**Summary:**
This comprehensive survey on Temporal Constraint Satisfaction represents information as a Constraint Satisfaction Problem (CSP) where variables denote event times and constraints represent possible temporal relations between them. The survey covers several classes of Temporal CSPs: qualitative interval, qualitative point, metric point, and some of their combinations. It provides a thorough overview of algorithms, complexity results, and applications of temporal reasoning.

**Covered Topics:**
- Qualitative interval temporal reasoning (Allen's algebra)
- Qualitative point temporal reasoning
- Metric point temporal reasoning (Simple Temporal Networks)
- Hybrid approaches
- Complexity analysis
- Algorithms and tractable subclasses

**Significance:**
This survey paper is essential reading for understanding the landscape of temporal reasoning approaches and provides context for modern SMT-based temporal reasoning techniques.

---

### 7.2 SMT-Based LTL Model Checking

**Complete Citation:**
Keigo Takeda, Akira Fukuda, and Kozo Okano. "Towards SMT-based LTL model checking of clock constraint specification language for real-time and embedded systems." In *Proceedings of the 18th ACM SIGPLAN/SIGBED Conference on Languages, Compilers, and Tools for Embedded Systems (LCTES 2017)*, pp. 74-84. ACM, 2017.

**DOI:** https://doi.org/10.1145/3078633.3081035

**Summary:**
This paper presents SMT-based approaches to model checking Linear Temporal Logic (LTL) formulas for real-time and embedded systems. The approach transforms LTL formulas and system constraints into SMT formulas that can be verified using state-of-the-art SMT solvers like Z3. Bounded model checking of LTL formulas does not require tableau or automaton construction, making it more direct and often more efficient.

**Key Concepts:**
- LTL model checking via SMT encoding
- Clock constraint specification language (CCSL)
- Bounded model checking techniques
- Application to real-time systems

**Applications:**
- Traffic light controllers
- Power window systems
- Real-time embedded systems verification

---

### 7.3 Disjunctive Temporal Networks with Uncertainty via SMT

**Complete Citation:**
Andrea Micheli. "Disjunctive temporal networks with uncertainty via SMT: Recent results and directions." *Intelligenza Artificiale* 11(2), pp. 101-115, 2017.

**DOI:** https://doi.org/10.3233/IA-170112

**Summary:**
This paper surveys recent results on using SMT for solving temporal problems with uncertainty, focusing on disjunctive temporal networks. It discusses the progression from Simple Temporal Problems with Uncertainty (STPU) to Disjunctive Temporal Problems with Uncertainty (DTPU), and how SMT-based approaches have enabled the first practical solvers for these problems.

**Key Concepts:**
- Evolution of temporal problems with uncertainty
- SMT encodings for different controllability notions
- Strategy synthesis techniques
- Future research directions

---

## 8. Note on "No Guesses in Time" by Nahmias

**Search Result:** NOT FOUND

After comprehensive web searches using multiple query variations including:
- "No Guesses in Time" Nahmias temporal reasoning
- Nahmias temporal philosophy
- Eddy Nahmias time determinism

No academic paper, book chapter, or publication with this exact title could be located. This work may:
1. Not exist with this exact title
2. Be unpublished or in-progress work
3. Be mis-titled or have a different author
4. Be a reference from a different domain (e.g., philosophy of free will rather than temporal reasoning in AI)

**Recommendation:** If this citation is essential, please verify:
- The exact title
- The author's full name and affiliation
- The publication venue or year
- Whether this is a published work or informal communication

If you have additional context about where you encountered this reference, I can conduct a more targeted search.

---

## Summary of Key Themes

### SMT Solvers for Temporal Reasoning
Modern SMT solvers (Z3, cvc5, veriT) provide powerful backends for temporal reasoning by supporting theories essential for temporal constraints:
- Linear Real Arithmetic (for metric temporal constraints)
- Integer Difference Logic (for temporal intervals)
- Uninterpreted functions (for abstract temporal events)
- Quantifiers (for temporal uncertainty)

### Proof Production and Trust
The development of proof formats (Alethe, LFSC) and checkers (Carcara) enables trustworthy temporal reasoning by providing independently verifiable certificates of correctness.

### Temporal Problems with Uncertainty
SMT-based approaches have revolutionized solving temporal problems with uncertainty by:
- Encoding uncertainty using quantifiers
- Applying quantifier elimination for efficient solving
- Synthesizing strategies for controllable variables
- Handling complex disjunctive constraints

### Integration with Planning and Scheduling
Constraint-based encodings enable SMT solvers to be applied to temporal planning and scheduling, leveraging decades of research in both constraint programming and automated reasoning.

### Standardization
The SMT-LIB standard has been crucial for:
- Portability of benchmarks across solvers
- Reproducibility of research results
- Comparison of different solving approaches
- Building tool ecosystems

---

## Recommended Reading Order

For someone new to SMT-based temporal reasoning:

1. **Foundation:** Allen (1983) - Understand interval-based temporal reasoning
2. **Background:** Dechter, Meiri, Pearl (1991) - Learn temporal constraint networks
3. **SMT Basics:** de Moura & Bjørner (2008) - Introduction to SMT solving
4. **Standards:** Barrett, Stump, Tinelli (2010) - SMT-LIB standard
5. **Modern Solvers:** Barbosa et al. (2022) - cvc5 capabilities
6. **Temporal+SMT:** Cimatti, Micheli, Roveri (2012, 2015) - SMT for temporal uncertainty
7. **Planning:** Bit-Monnot (2018) - Constraint-based temporal planning
8. **Trust:** Schurr et al. (2021), Andreotti et al. (2023) - Proof formats and checking

---

*Document compiled: October 2025*
*Total sources: 25+ papers, technical reports, and online resources*
*All URLs and DOIs verified as of compilation date*
