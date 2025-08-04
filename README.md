# Formalizing Finite Ramsey Theory Using Lean 4 

We combinte automated and interactive theorm proving (in Lean 4) to
formalize finite Ramsey theorey. We prove exact values for several
small Ramsey numbers and related van der Waerden numbers.

## Van der Waerden's theorem

The statement of the theorem is [here](https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem).

In ```VdW.lean```, the first major result was formalzing $W(2,3) <=
325$ by interactive theorem proving.

The second major contribution so far was formalizing $W(2,3) = 9$, in
which we proved the lowerbound by brute force and the upperbound by
automated reasoning (via SAT solving).

## Ramsey Theory 

The statement of the theorem is [here](https://en.wikipedia.org/wiki/Ramsey%27s_theorem). 

The development is divided into several theories:

* The `RamseyGraphs.lean` theory interprets Ramsey's theorem as a
  theorem about cliques and independent sets.
  
* The `RamseyBase.lean` theory defines the basics of multicolor Ramsey
  theory and proves some basic facts about the definition.
  
* The `Ramsey2Color.lean` theory depends on the `RamseyBase.lean`
  theory and specializes it to 2 colors. This theory contains the
  proofs of exact Ramsey numbers of the form `R(s,t)`. It uses
  theorems from the `RamseyGraphs.lean` to establish those results.
  
* The more general theory is `Ramsey.lean` which proves statements
  about multicolor Ramsey numbers. It also contains the proof of
  `R(3,3,3)=17`.

## G6 Graphs and Graph Visualization Widget

To easily refer to graphs in the various theorems where graphs serve
as witnesses, we use the g6 format from [nauty](https://pallini.di.uniroma1.it/Guide.html).

In order to visualize those graphs, we developed a Lean Widget in
`G6Visualizer.lean`.

## Verified Encodders

To obtain verifiable correct encodings of the Ramsey property as a Boolean formula in CNF run

```
lake exe RamseyEncoder <N> <s> <t>
```

The formula output will be satisfiable iff the number `N+1` does not
have the Ramsey property. This is proven in the [trestle](https://github.com/FormalSAT/trestle) framework.
