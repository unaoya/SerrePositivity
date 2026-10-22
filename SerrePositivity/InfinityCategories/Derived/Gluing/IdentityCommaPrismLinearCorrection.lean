module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismLinearDifference
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexLinearHEq
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismLinearCorrection

/-! 明示 prism の実出力の差を、零補正または元 primitive の単一成分へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)

lemma dgGluingIdentityCommaPrism_component_of_correction_zero
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' hJ) = 0)
    (hz : dgGluingCommaPrismCorrectionSum R E E (DGFunctor.id E) s.val.toSimplexData
      (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
      (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
      (by rw [card_withLast]; omega) = 0) :
    (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk =
      dgGluingIdentityCommaReplacementComponent R E s J k hJ hk := by
  have hd := dgGluingIdentityCommaPrism_component_difference R E s β J k hJ hk hβ
  have hzero := dgGluingGradedHom_zero_heq (R := R) (E := E)
    (congrArg (fun Z : DGFunctorCommaObject R E E (DGFunctor.id E) => Z.replacement)
      (source_obj s (J.min' hJ)))
    (congrArg (fun Z : DGFunctorCommaObject R E E (DGFunctor.id E) => Z.source) (target_obj s))
    (p := k) rfl
  exact sub_eq_zero.mp (eq_of_heq (hd.trans ((heq_of_eq hz).trans hzero)))

lemma dgGluingIdentityCommaPrism_component_correction
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' (Index.nonempty hJ)) = 0)
    (hsecond : β (second J hJ) = 1) :
    HEq ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k
        (Index.nonempty hJ) hk -
        dgGluingIdentityCommaReplacementComponent R E s J k (Index.nonempty hJ) hk)
      ((((withLast J).filter ((second J hJ).castSucc < ·)).card : ℤ).negOnePow •
        dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) (k + 1)
          ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
            (LinearData.erase_nonempty hJ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ)); omega))) := by
  have hd := dgGluingIdentityCommaPrism_component_difference R E s β J k
    (Index.nonempty hJ) hk hβ
  have hs := dgGluingCommaPinchedPrismCorrectionSum_second R E E (DGFunctor.id E) s
    (pinchedPrismPhase β) J hJ k hk
  rw [pinchedPrismPhase_castSucc, ite_eq_left hsecond] at hs
  exact hd.trans ((heq_of_eq hs).trans
    ((dgGluingCommaPinchedPrismCut_second R E E (DGFunctor.id E) s J hJ k hk).trans
      (dgGluingCommaPinchedPrismRightCorrection_linear R E E (DGFunctor.id E) s J hJ k hk)))

end SerrePositivity.InfinityCategories
