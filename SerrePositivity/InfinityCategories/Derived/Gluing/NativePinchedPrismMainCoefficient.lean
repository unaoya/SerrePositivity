module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismMainLinear
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedProjectionComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.ActionYonedaInverse

/-! 元 gluing augmentation prism の実主項は、元の左作用 νf の全次数の Yoneda 像である。 -/
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

lemma dgGluingNativePinchedPrismMain_coefficient
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgGluingCommaPrismMainCoefficient R D (RightModule R C) M.toFunctor
        (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData (withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _)
        (max_withLast J _) (by rw [card_withLast]; omega))
      ((dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        ((dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y).f k
          ((toLinearData s).component J k hJ hk))) := by
  have h := dgGluingCommaPinchedPrismMain_linear R D (RightModule R C) M.toFunctor
    (dgGluingNativeCommaPinchedSimplex R C D M s) J k hJ hk
  rw [dgGluingNativePinchedReplacement_component R C D M s J k hJ hk] at h
  refine h.trans (heq_of_eq ?_)
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingLeftAction_yoneda_inverse R C D M X Y) k)
      ((dgGluingLeftHomMap R C D M X Y).f k ((toLinearData s).component J k hJ hk))).symm

end SerrePositivity.InfinityCategories
