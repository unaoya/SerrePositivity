module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndComparisonSurjective
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonFibers

/-!
概要：同じ生成圏を回収する Ind 比較の、生成対象間の元の写像空間比較は同値。
方針：回収の全自然同型と生成関手の充満忠実性を、元の合成の二対三則へ渡す。
規約：任意の Ind 対象への拡張は未証明。生成対象間の実際の pinchedHomMap を扱う。
使われ方：Ind 比較の全充満忠実性を compact 性と密度で証明するための初期条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 同じ比較関手は、元の二つの Yoneda 生成対象間の全写像空間で同値を誘導する。 -/
lemma indComparison_generator_pinchedHomMap_isEquivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} (hi : IsFullyFaithful i)
    {G : Ind.IndInfinity κ A ⟶ C} (e : FunctorIso (Ind.indYoneda κ A ≫ G) i)
    (a b : A _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap G
      ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a))
      ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up b))) := by
  have h := ((e.isFullyFaithful_iff).mpr hi) (ULift.up a) (ULift.up b)
  rw [pinchedHomMap_comp] at h
  exact (Ind.indYoneda_isFullyFaithful κ A (ULift.up a) (ULift.up b)).cancel_left h

/-- 同じ二生成対象上では、比較の実 coslice fiber 射そのものが同値。 -/
lemma indComparison_generator_cosliceFiber_isEquivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} (hi : IsFullyFaithful i)
    {G : Ind.IndInfinity κ A ⟶ C} (e : FunctorIso (Ind.indYoneda κ A ≫ G) i)
    (a b : A _⦋0⦌) :
    let x := (Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)
    let y := (Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up b)
    IsQCatEquivalence (vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (Limits.pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G)
      (cosliceComparisonOver G x) (cosliceComparisonOver_projection G x) y) := by
  dsimp only
  exact (cosliceComparisonOver_fiber_equivalence_iff G _ _).mpr
    (indComparison_generator_pinchedHomMap_isEquivalence hi e a b)

end SerrePositivity.InfinityCategories.F2.Presentable
