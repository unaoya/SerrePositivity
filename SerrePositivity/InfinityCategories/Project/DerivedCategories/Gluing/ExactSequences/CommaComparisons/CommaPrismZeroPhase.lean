module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaPinchedPrismMixedCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedPrismPhase

/-! 標的だけ相一の prism では内部切断の相は零であり、全補正和が消える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n + 1))

lemma dgGluingCommaPrismCorrectionSum_zeroPhase
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismCorrectionSum R C E F s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a b k hI ha hb hk = 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismCorrectionSum]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · have hjlast : j ≠ Fin.last (n + 1) := ne_of_lt (h.2.1.trans_le (Fin.le_last b))
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hjlast
    have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc
      (OrderHom.const (Fin (n + 1)) (0 : Fin 2)) j
    have hf : (0 : Fin 2) = 1 := hz.symm.trans h.2.2
    exact False.elim (Fin.zero_ne_one hf)
  · rfl

lemma dgGluingCommaPrismMixedHom_zeroPhase
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a b k hI ha hb hk =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMainCoefficient R C E F s I a b k hI ha hb hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMixedCoefficient_eq,
    dgGluingCommaPrismCorrectionSum_zeroPhase R C E F s I a b k hI ha hb hk, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
