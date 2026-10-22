module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismObjects
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedSourceComponent
public import SerrePositivity.InfinityCategories.Derived.Gluing.ActionYonedaInverse

/-! 元 augmentation prism の相一の実係数を、右射影と augmentation の閉前合成へ戻す。 -/
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

lemma dgGluingNativePinchedPrism_one_coefficient
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' hJ) = 1) :
    HEq ((dgGluingNativePinchedPrismSimplex R C D M s β).hom (withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _)
        (max_withLast J _) (by rw [card_withLast]; omega))
      ((M.toFunctor.map X.right Y.right).f k ((dgGluingRightHomMap R C D M X Y).f k
        ((toLinearData s).component J k hJ hk))) := by
  have he := congrArg (fun t => dgCommaAugmentationPrismSimplex R D (RightModule R C)
    M.toFunctor t (pinchedPrismPhase β)) (dgGluingNativeCommaPinchedSimplex_val R C D M s).symm
  have ha := Simplex.hom_heq_of_eq he (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
    (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega)
  have hb := dgCommaAugmentationPrismData_hom_one R D (RightModule R C) M.toFunctor
    (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData (pinchedPrismPhase β)
    (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ)
    (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega)
    ((pinchedPrismPhase_castSucc β _).trans hβ) (pinchedPrismPhase_last β)
  have hc := dgGluingFunctor_map_component_heq
    (dgCommaAugmentationTarget R D (RightModule R C) M.toFunctor)
    (source_obj (dgGluingNativeCommaPinchedSimplex R C D M s) (J.min' hJ))
    (target_obj (dgGluingNativeCommaPinchedSimplex R C D M s)) k
    (toLinearData_component_heq (dgGluingNativeCommaPinchedSimplex R C D M s) J k hJ hk).symm
  have hv : ((dgCommaAugmentationTarget R D (RightModule R C) M.toFunctor).map
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)).f k
      ((toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J k hJ hk) =
      (M.toFunctor.map X.right Y.right).f k ((dgGluingRightHomMap R C D M X Y).f k
        ((toLinearData s).component J k hJ hk)) := by
    change (M.toFunctor.map X.right Y.right).f k
      ((dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor _ _).f k
        ((toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J k hJ hk)) = _
    rw [dgGluingNativePinchedSource_component]
  exact ha.trans (hb.trans (hc.trans (heq_of_eq hv)))

end SerrePositivity.InfinityCategories
