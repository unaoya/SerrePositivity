module
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismCutCoordinates

/-! pinched prism の区間評価では、終端相一延長は二つの時間の上限となる。 -/
@[expose] public section
namespace SerrePositivity.InfinityCategories

lemma dgGluingPinchedPrismPhase_cut {n : ℕ}
    (β t : Fin (n + 1) →o Fin 2) :
    (pinchedPrismPhase β).comp (coherentPrismCut t) = β ⊔ t := by
  apply DFunLike.ext
  intro i
  change pinchedPrismPhase β (coherentPrismCut t i) = max (β i) (t i)
  by_cases hi : t i = 0
  · rw [coherentPrismCut_zero t i hi, pinchedPrismPhase_castSucc]
    rw [hi, max_eq_left (Fin.zero_le _)]
  · rw [coherentPrismCut_one t i hi, pinchedPrismPhase_last]
    have h1 : t i = 1 := by omega
    rw [h1, max_eq_right (show β i ≤ (1 : Fin 2) by omega)]

lemma dgGluingCoherentPrismCut_terminal {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) {i j : Fin (n + 1)}
    (hij : i ≤ j) (hi : t i ≠ 0) :
    coherentPrismCut t i = coherentPrismCut t j := by
  have hj : t j ≠ 0 := by
    intro hj
    exact hi (le_antisymm (hj ▸ t.monotone hij) (Fin.zero_le _))
  rw [coherentPrismCut_one t i hi, coherentPrismCut_one t j hj]

end SerrePositivity.InfinityCategories
