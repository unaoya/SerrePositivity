module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismActualCoefficients
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase

/-! 元 gluing augmentation prism の始終対象を、同じ元対象の augmentation の二端へ戻す。 -/
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

abbrev dgGluingNativePinchedPrismSimplex (β : Fin (n + 1) →o Fin 2) :=
  dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
    (s.val.map (dgGluingToComma R C D M)) (pinchedPrismPhase β)

lemma dgGluingNativePinchedPrism_target (β : Fin (n + 1) →o Fin 2) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj (Fin.last (n + 1)) =
      M.rightAt Y.right := by
  change (dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (dgGluingToComma R C D M)).toSimplexData (pinchedPrismPhase β)).obj
    (Fin.last (n + 1)) = _
  rw [dgCommaAugmentationPrismData_obj_one R D (RightModule R C) M.toFunctor _ _ _
    (pinchedPrismPhase_last β)]
  change M.rightAt (s.val.obj (Fin.last (n + 1))).right = _
  rw [target_obj s]

lemma dgGluingNativePinchedPrism_source_zero (β : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hβ : β i = 0) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj i.castSucc = representable R X.left := by
  change (dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (dgGluingToComma R C D M)).toSimplexData (pinchedPrismPhase β)).obj
    i.castSucc = _
  rw [dgCommaAugmentationPrismData_obj_zero R D (RightModule R C) M.toFunctor _ _ _
    ((pinchedPrismPhase_castSucc β i).trans hβ)]
  change representable R (s.val.obj i.castSucc).left = _
  rw [source_obj s i]

lemma dgGluingNativePinchedPrism_source_one (β : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hβ : β i = 1) :
    (dgGluingNativePinchedPrismSimplex R C D M s β).obj i.castSucc = M.rightAt X.right := by
  change (dgCommaAugmentationPrismData R D (RightModule R C) M.toFunctor
    (s.val.map (dgGluingToComma R C D M)).toSimplexData (pinchedPrismPhase β)).obj
    i.castSucc = _
  rw [dgCommaAugmentationPrismData_obj_one R D (RightModule R C) M.toFunctor _ _ _
    ((pinchedPrismPhase_castSucc β i).trans hβ)]
  change M.rightAt (s.val.obj i.castSucc).right = _
  rw [source_obj s i]

end SerrePositivity.InfinityCategories
