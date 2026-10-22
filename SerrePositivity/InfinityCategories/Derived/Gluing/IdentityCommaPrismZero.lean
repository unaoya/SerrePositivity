module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismZeroCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.SimplexCoefficientExt

/-! 固定標的の augmentation が恒等なら、元の全 prism の零端は実 replacement 射影そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingIdentityCommaPrism_zero {n : ℕ}
    (s : Simplex R (DGFunctorCommaObject R E E (DGFunctor.id E)) (n + 1))
    (y : E) (hy : s.obj (Fin.last (n + 1)) = dgGluingIdentityCommaObject R E y) :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s
      (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) =
        s.map (dgCommaAugmentationSource R E E (DGFunctor.id E)) := by
  apply dgGluingSimplex_ext_coefficients
  · intro i
    induction i using Fin.lastCases with
    | last =>
      change StrictNatTrans.phaseObj (dgCommaAugmentationSource R E E (DGFunctor.id E))
        (dgCommaAugmentationTarget R E E (DGFunctor.id E))
        (pinchedPrismPhase _ (Fin.last (n + 1))) (s.obj (Fin.last (n + 1))) =
          (s.obj (Fin.last (n + 1))).replacement
      rw [pinchedPrismPhase_last, hy]
      rfl
    | cast i =>
      change StrictNatTrans.phaseObj (dgCommaAugmentationSource R E E (DGFunctor.id E))
        (dgCommaAugmentationTarget R E E (DGFunctor.id E))
        (pinchedPrismPhase _ i.castSucc) (s.obj i.castSucc) = (s.obj i.castSucc).replacement
      rw [pinchedPrismPhase_castSucc]
      rfl
  · intro I a b k hI ha hb hk
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card hI
    have haLast : a ≠ Fin.last (n + 1) := ne_of_lt (hab.trans_le (Fin.le_last b))
    obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last haLast
    induction b using Fin.lastCases with
    | last =>
      exact (dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
        (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a.castSucc
        (Fin.last (n + 1)) k hI ha hb hk (pinchedPrismPhase_castSucc _ a)
        (pinchedPrismPhase_last _)).trans
          (dgGluingIdentityCommaPrismMixed_target R E s.toSimplexData I a.castSucc
            (Fin.last (n + 1)) k hI ha hb hk y hy)
    | cast b =>
      exact dgCommaAugmentationPrismData_hom_zero R E E (DGFunctor.id E) s.toSimplexData
        (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a.castSucc b.castSucc
        k hI ha hb hk (pinchedPrismPhase_castSucc _ a) (pinchedPrismPhase_castSucc _ b)

end SerrePositivity.InfinityCategories
