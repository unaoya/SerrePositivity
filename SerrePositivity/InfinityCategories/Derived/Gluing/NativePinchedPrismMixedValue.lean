module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismMainCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrectionValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismActualCoefficients

/-! 元 augmentation prism の実混合係数を、νf と元 Hom primitive の同じ固定次数和へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePinchedPrism_mixed_value
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' hJ) = 0) :
    HEq ((dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.val.map (dgGluingToComma R C D M)) (pinchedPrismPhase β)).hom
        (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega))
      ((dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        (((dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y).f k
            ((toLinearData s).component J k hJ hk)) +
          dgGluingNativePrismCorrectionValue R C D M s β J k hk)) := by
  have hc := dgGluingNativePinchedPrismActual_mixed R C D M s (pinchedPrismPhase β)
    (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ)
    (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega)
    ((pinchedPrismPhase_castSucc β _).trans hβ) (pinchedPrismPhase_last β)
  have hs := gradedHom_add_heq
    (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor => Z.replacement)
      (source_obj (dgGluingNativeCommaPinchedSimplex R C D M s) (J.min' hJ)))
    (congrArg (fun Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor =>
      M.toFunctor.obj Z.source) (target_obj (dgGluingNativeCommaPinchedSimplex R C D M s)))
    (k := k) rfl _ _ _ _
    (dgGluingNativePinchedPrismMain_coefficient R C D M s J k hJ hk)
    (dgGluingNativePinchedPrismCorrectionSum_value R C D M s β J k hJ hk)
  refine hc.trans (hs.trans (heq_of_eq ?_))
  simp only [map_add]

end SerrePositivity.InfinityCategories
