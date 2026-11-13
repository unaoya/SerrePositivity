module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaPrismZeroCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Coefficients.SimplexCoefficientExt

/-! 固定標的の augmentation が恒等なら、元の全 prism の零端は実 replacement 射影そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingIdentityCommaPrism_zero {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) (n + 1))
    (y : E) (hy : s.obj (Fin.last (n + 1)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) =
        s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplex_ext_coefficients
  · intro i
    induction i using Fin.lastCases with
    | last =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase _ (Fin.last (n + 1))) (s.obj (Fin.last (n + 1))) =
          (s.obj (Fin.last (n + 1))).replacement
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last, hy]
      rfl
    | cast i =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase _ i.castSucc) (s.obj i.castSucc) = (s.obj i.castSucc).replacement
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc]
      rfl
  · intro I a b k hI ha hb hk
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card hI
    have haLast : a ≠ Fin.last (n + 1) := ne_of_lt (hab.trans_le (Fin.le_last b))
    obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last haLast
    induction b using Fin.lastCases with
    | last =>
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a.castSucc
        (Fin.last (n + 1)) k hI ha hb hk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last _)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrismMixed_target R E s.toSimplexData I a.castSucc
            (Fin.last (n + 1)) k hI ha hb hk y hy)
    | cast b =>
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_zero R E E (DGFunctor.id E) s.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a.castSucc b.castSucc
        k hI ha hb hk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ b)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
