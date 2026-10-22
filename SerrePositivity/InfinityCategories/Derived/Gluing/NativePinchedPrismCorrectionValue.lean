module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrectionSum
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismCorrectionEdge
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainDegreeHEq
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase

/-! 元 Hom primitive の同じ唯一切断を固定 Hom 次数に置き、実 prism の全補正和を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativePrismCorrectionValue (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (M.value X.left Y.right).X k :=
  if h₂ : 2 ≤ J.card then
    if β (second J h₂) = 1 then
      (((withLast J).filter ((second J h₂).castSucc < ·)).card : ℤ).negOnePow •
        (dgGluingHomPrimitive R C D M X Y).v (k + 1) k (by omega)
          ((toLinearData s).component (J.erase (J.min' (Index.nonempty h₂))) (k + 1)
            (LinearData.erase_nonempty h₂ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty h₂)); omega))
    else 0
  else 0

lemma dgGluingNativePinchedPrismCorrectionSum_value
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgGluingCommaPrismCorrectionSum R D (RightModule R C) M.toFunctor
        (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData
        (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega))
      ((dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        (dgGluingNativePrismCorrectionValue R C D M s β J k hk)) := by
  by_cases h₂ : 2 ≤ J.card
  · by_cases hs : β (second J h₂) = 1
    · rw [dgGluingNativePrismCorrectionValue, dite_eq_left h₂, ite_eq_left hs]
      have hc := dgGluingNativePinchedPrismCorrectionSum_primitive R C D M s
        (pinchedPrismPhase β) J h₂ k hk ((pinchedPrismPhase_castSucc β _).trans hs)
      have hd := dgGluingCochain_post_smul_heq (dgGluingHomPrimitive R C D M X Y)
        (dgYonedaIso R X.left (M.rightAt Y.right)).inv (p := k + 1) (q := k + 1 - 1)
        (q' := k) (by omega)
        ((toLinearData s).component (J.erase (J.min' (Index.nonempty h₂))) (k + 1)
          (LinearData.erase_nonempty h₂ _ (J.min'_mem _))
          (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty h₂)); omega))
        (by omega) (by omega)
        ((((withLast J).filter ((second J h₂).castSucc < ·)).card : ℤ).negOnePow)
      refine hc.trans (hd.trans (heq_of_eq ?_))
      simp only [Units.smul_def, map_zsmul]
    · have hc := dgGluingNativePinchedPrismCorrectionSum_zero R C D M s
        (pinchedPrismPhase β) J h₂ k hk (by simpa only [pinchedPrismPhase_castSucc] using hs)
      rw [dgGluingNativePrismCorrectionValue, dite_eq_left h₂, ite_eq_right hs, map_zero]
      exact (heq_of_eq hc).trans (dgGluingGradedHom_zero_heq (R := R) (E := RightModule R C)
        (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor => Z.replacement)
          (source_obj (dgGluingNativeCommaPinchedSimplex R C D M s) (J.min' hJ)))
        (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor =>
          M.toFunctor.obj Z.source) (target_obj (dgGluingNativeCommaPinchedSimplex R C D M s))) rfl)
  · rw [dgGluingNativePrismCorrectionValue, dite_eq_right h₂, map_zero]
    have hcard : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
    have hc := dgGluingCommaPrismCorrectionSum_card_two R D (RightModule R C) M.toFunctor
      (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData (pinchedPrismPhase β)
      (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ)
      (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega)
      (by rw [card_withLast, hcard])
    exact (heq_of_eq hc).trans (dgGluingGradedHom_zero_heq (R := R) (E := RightModule R C)
      (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor => Z.replacement)
        (source_obj (dgGluingNativeCommaPinchedSimplex R C D M s) (J.min' hJ)))
      (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor =>
        M.toFunctor.obj Z.source) (target_obj (dgGluingNativeCommaPinchedSimplex R C D M s))) rfl)

end SerrePositivity.InfinityCategories
