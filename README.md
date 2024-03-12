# Formalizing Finite Ramsey Theory Using Lean 4 
This ongoing project is a joint work by **David Narvez, Congyan (Cruise) Song, and Ningxin Zhang**. We use **interactive theorm proving (in Lean 4)** combined with **automated theorem proving** to formalize finite Ramsey theorey. We prove exact values for several small Ramsey numbers and related van der Waerden numbers. 

## Van der Waerden's theorem
The statement of the theorem is at [here](https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem). 

In ```VdW.lean```, the first major result was formalzing $W(2,3) <= 325$ by interactive theorem proving.

The second major contribution so far was formalizing $W(2,3) = 9$, in which we proved the lowerbound by brutal force and the upperbound by automated theorem proving by SAT solveres.

## Ramsey Theory 
The statement of the theorem is at [here](https://en.wikipedia.org/wiki/Ramsey%27s_theorem). 

In ```Ramsey2Color.lean``` We proved a series of theorems with small Ramsey numbers, including the exact values such as $R(3,3) = 6$. 

To fully understand the details of our proof, one might find it helpful to read ```Utils.lean```, in which we put some definitions and interesting lemmas. 

## Pick Tactic
We designed a powerful pick tactic to pick distinct elements from a multiset (based on Generalized Pigeonhole Principle), see ```PickTactic.lean```.

## Widget
In order to provide visualization for the graphs in our proofs, we built a Lean Widget in ```G6Visualizer```.

## Usage
First, install Lean 4 following the instructions from [here](https://github.com/leanprover/lean4).

Then clone the project onto your computer e.g. with ```git clone https://github.com/cruisesong7/formal_ramsey.git```.

