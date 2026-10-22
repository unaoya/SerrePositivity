module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplex
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeAugmentationPrimitive
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismLinearCorrection

/-! 元の augmentation prism の唯一の補正を、元 gluing Hom の実 primitive の Yoneda 像へ戻す。 -/
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

def dgGluingNativeCommaPinchedSimplex :
    (DGNerve.pinchedHom R (DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
      (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)) _⦋n⦌ :=
  dgGluingFunctorPinchedSimplex.{u, max u v w, max (u + 1) v w, 0}
    (dgGluingToComma R C D M) s

lemma dgGluingNativeCommaPinchedSimplex_val :
    (dgGluingNativeCommaPinchedSimplex R C D M s).val = s.val.map (dgGluingToComma R C D M) :=
  dgGluingFunctorPinchedSimplex_val _ _

lemma dgGluingNativePinchedAugmentationComponent
    (J : Finset (Fin (n + 1))) (p : ℤ) (hJ : J.Nonempty) (hp : p = 1 - (J.card : ℤ)) :
    dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) p
        ((toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J p hJ hp) =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        ((dgGluingHomPrimitive R C D M X Y).v p (p - 1) (by omega)
          ((toLinearData s).component J p hJ hp)) := by
  have h := dgGluingFunctorPinchedSimplex_component.{u, max u v w, max (u + 1) v w, 0}
    (dgGluingToComma R C D M) s J p hJ hp
  change (toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J p hJ hp =
    ((dgGluingToComma R C D M).map X Y).f p ((toLinearData s).component J p hJ hp) at h
  rw [h]
  exact dgGluingNativeAugmentationHomotopyComponent R C D M X Y p _

lemma dgGluingNativePinchedPrismRightCorrection_primitive
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgGluingCommaPrismRightCorrection R D (RightModule R C) M.toFunctor
        (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData (withLast J)
        (Fin.last (n + 1)) (two_withLast (Index.nonempty hJ)) (max_withLast J _)
        (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩)) (Fin.castSucc_lt_last _))
      ((((withLast J).filter ((second J hJ).castSucc < ·)).card : ℤ).negOnePow •
        (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (k + 1 - 1)
          ((dgGluingHomPrimitive R C D M X Y).v (k + 1) (k + 1 - 1) (by omega)
            ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
              (LinearData.erase_nonempty hJ _ (J.min'_mem _))
              (by
                have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ))
                omega)))) := by
  refine (dgGluingCommaPinchedPrismRightCorrection_linear R D (RightModule R C) M.toFunctor
    (dgGluingNativeCommaPinchedSimplex R C D M s) J hJ k hk).trans ?_
  apply heq_of_eq
  exact congrArg (fun z =>
    (((withLast J).filter ((second J hJ).castSucc < ·)).card : ℤ).negOnePow • z)
    (dgGluingNativePinchedAugmentationComponent R C D M s _ (k + 1) _ _)

end SerrePositivity.InfinityCategories
