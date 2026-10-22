module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrection
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections

/-! 元 pinched Hom の実 comma 像の replacement 射影を、同じ左 Hom 鎖射影と Yoneda 像へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom HomologicalComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePinchedReplacement_component
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    ((dgCommaAugmentationSource R D (RightModule R C) M.toFunctor).map
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)).f k
      ((toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J k hJ hk) =
    (yonedaHom R C X.left Y.left).f k
      ((dgGluingLeftHomMap R C D M X Y).f k ((toLinearData s).component J k hJ hk)) := by
  have h := dgGluingFunctorPinchedSimplex_component.{u, max u v w, max (u + 1) v w, 0}
    (dgGluingToComma R C D M) s J k hJ hk
  change (toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J k hJ hk =
    ((dgGluingToComma R C D M).map X Y).f k ((toLinearData s).component J k hJ hk) at h
  rw [h]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingHomRepresentableIso_left R C D M X Y) k)
      ((toLinearData s).component J k hJ hk)

end SerrePositivity.InfinityCategories
