import Mathlib.Tactic.FinCases

-- NOTE: This is in Mathlib.LinearAlgebra.AffineSpace.Combination
-- but we would like to use this fact without invoking 50 Gb of math
theorem univ_fin2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
  ext x
  fin_cases x <;> simp

lemma notc : ∀ {c x y : Fin 2}, x ≠ c → y ≠ c → x = y := by

  intros c x y _ _
  fin_cases c 
  all_goals{
    fin_cases x 
    try{tauto}
    fin_cases y 
    all_goals{
      tauto
    }
  }
  done

lemma not0_eq1: ∀ {x: Fin 2}, x ≠ 0 ↔ x = 1 := by
  intro 
  apply Iff.intro 
  · intro xneq0
    have _1_neq0 : (1 : Fin 2) ≠ 0 := by simp
    apply notc xneq0 _1_neq0
  · intro
    simp_all
  done
