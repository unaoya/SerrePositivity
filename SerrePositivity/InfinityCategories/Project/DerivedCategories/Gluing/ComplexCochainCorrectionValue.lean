module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainPrismComponentFormula

/-! 一切断の補正値を任意の複体に置き、実鎖写像による後合成との厳密な自然性を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  {a b : C} {L Q : _root_.SerrePositivity.DifferentialGraded.Complex R} (h : Cochain (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) L (-1)) {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C a b) _⦋n⦌)

def dgGluingComplexCochainCorrectionValue (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) : L.X k :=
  if h₂ : 2 ≤ J.card then
    if β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J h₂) = 1 then
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J h₂).castSucc < ·)).card : ℤ).negOnePow •
        -h.v (k + 1) k (by omega)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty h₂))) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty h₂ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty h₂)); omega))
    else 0
  else 0

lemma dgGluingComplexCochainCorrectionValue_post (q : L ⟶ Q)
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    q.f k (dgGluingComplexCochainCorrectionValue R C h s β J k hk) =
      dgGluingComplexCochainCorrectionValue R C
        (h.comp (Cochain.ofHom q) (add_zero (-1))) s β J k hk := by
  by_cases h₂ : 2 ≤ J.card
  · by_cases hs : β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J h₂) = 1
    · simp only [dgGluingComplexCochainCorrectionValue, dite_eq_left h₂, ite_eq_left hs,
        Units.smul_def, map_zsmul, map_neg, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        ModuleCat.comp_apply]
    · simp only [dgGluingComplexCochainCorrectionValue, dite_eq_left h₂, ite_eq_right hs, map_zero]
  · simp only [dgGluingComplexCochainCorrectionValue, dite_eq_right h₂, map_zero]

lemma dgGluingCochainPrismCorrectionValue_eq_complex
    {E : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (x y : E)
    (h' : Cochain (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1))
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPrismCorrectionValue R C E x y h' s β J k hk =
      dgGluingComplexCochainCorrectionValue R C h' s β J k hk := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
