module

public import SerrePositivity.InfinityCategories.F1.RepresentablePresheafSliceComparison
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.PresheafRestrictionEquivalence

/-!
概要：実際の Yoneda 対象前層の小さい unstraightening と元の表現可能射影を比較する。
方針：元の slice の分類図式の復元に、同じ前層との関手同型を合成してから反転する。
規約：両比較は元の底上の実際の射であり、対象の対応だけではない。
使われ方：表現可能 right fibration に対する Yoneda 評価の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の表現可能射影の反転から同じ Yoneda 前層の左 unstraightening への復元。 -/
def representableLeftUnstraighteningComparison
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (sliceOver (SSet.yonedaEquiv.symm y)).op ⟶
      smallLeftUnstraightening (representablePresheafInfinity y) :=
  leftStraighteningInfinityReconstruction
      (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y))) ≫
    smallLeftUnstraighteningComparisonOfFunctorIso (representablePresheafInfinity_sliceIso y).symm

/-- 左の比較は、元の反転した底を厳密に保つ。 -/
lemma representableLeftUnstraighteningComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    representableLeftUnstraighteningComparison y ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
    SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y)) := by
  rw [representableLeftUnstraighteningComparison, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    leftStraighteningInfinityReconstruction_projection]

/-- 同じ復元射は全空間の前合成同値。 -/
lemma representableLeftUnstraighteningComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (representableLeftUnstraighteningComparison y) :=
  (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence _).comp
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (smallLeftUnstraightening (representablePresheafInfinity y)) :=
  quasicategory_of_innerFibration
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))

/-- 同じ左の復元射は quasicategory の同値。 -/
lemma representableLeftUnstraighteningComparison_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsQCatEquivalence (representableLeftUnstraighteningComparison y) :=
  (representableLeftUnstraighteningComparison_isPrecompositionEquivalence y).isQCatEquivalence

/-- 元の表現可能 right fibration から、同じ Yoneda 前層の right unstraightening への比較。 -/
def representableRightUnstraighteningComparison
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    sliceOver (SSet.yonedaEquiv.symm y) ⟶
      smallRightUnstraightening (representablePresheafInfinity y) :=
  (SSet.opFunctorCompOpFunctorIso.app _).inv ≫
    SSet.opFunctor.map (representableLeftUnstraighteningComparison y)

/-- 右の比較は、元の底 C を厳密に保つ。 -/
lemma representableRightUnstraighteningComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    representableRightUnstraighteningComparison y ≫
      smallRightUnstraighteningProjection (representablePresheafInfinity y) =
    sliceOverProjection (SSet.yonedaEquiv.symm y) := by
  simp only [representableRightUnstraighteningComparison, smallRightUnstraighteningProjection,
    ← Category.assoc]
  rw [Category.assoc _ (SSet.opFunctor.map _) (SSet.opFunctor.map _), ← SSet.opFunctor.map_comp,
    representableLeftUnstraighteningComparison_projection]
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality
    (sliceOverProjection (SSet.yonedaEquiv.symm y))
  change SSet.opFunctor.map (SSet.opFunctor.map
      (sliceOverProjection (SSet.yonedaEquiv.symm y))) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom =
    (SSet.opFunctorCompOpFunctorIso.app (sliceOver (SSet.yonedaEquiv.symm y))).hom ≫
      sliceOverProjection (SSet.yonedaEquiv.symm y) at hn
  rw [Category.assoc, hn]
  exact (SSet.opFunctorCompOpFunctorIso.app
    (sliceOver (SSet.yonedaEquiv.symm y))).inv_hom_id_assoc _

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (smallRightUnstraightening (representablePresheafInfinity y)) :=
  quasicategory_of_innerFibration
    (smallRightUnstraighteningProjection (representablePresheafInfinity y))

/-- 元の right fibration と、同じ Yoneda 対象前層の right unstraightening の比較は同値。 -/
lemma representableRightUnstraighteningComparison_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsQCatEquivalence (representableRightUnstraighteningComparison y) := by
  let e : sliceOver (SSet.yonedaEquiv.symm y) ≅
      (sliceOver (SSet.yonedaEquiv.symm y)).op.op :=
    (SSet.opFunctorCompOpFunctorIso.app _).symm
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.comp
    (representableLeftUnstraighteningComparison_isQCatEquivalence y).opposite

end SerrePositivity.InfinityCategories
