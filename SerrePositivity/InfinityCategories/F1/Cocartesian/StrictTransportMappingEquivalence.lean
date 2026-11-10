module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PredicateIso
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativePrecompositionEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPredicateReflection
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldIso
public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cocartesian strict transport の元の全相対 Hom 作用は写像空間の同値。
方針：全相対 Hom の制限同値を水平辺条件へ制限し、scaffold 評価の同型を消去する。
規約：同値となる射は既に構成した同じ全高次の作用そのもの。
使われ方：Cat∞ 値 straightening の充満忠実性の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian 相対 Hom の universal scaffold への制限は同値。 -/
lemma cocartesianStrictTransportScaffoldRestriction_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C)
    [CocartesianFibration p] [CocartesianFibration q] :
    IsQCatEquivalence (cocartesianStrictTransportScaffoldRestriction p q) := by
  let R := relativeFunctorOverPre q (Over.homMk
    (U := Over.mk (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)))
    (V := Over.mk p) (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold p) (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_projection p))
  have hR : IsQCatEquivalence R :=
    relativeFunctorOverPre_isQCatEquivalence_of_cocartesian q _
      (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence p)
  apply isQCatEquivalence_fullSubcomplexRestriction
    (cocartesianRelativeFunctorPredicate p q)
    (CocartesianScaffoldFunctorPredicate (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p) q)
    (fun h => cocartesianScaffoldFunctorPredicate_iff_of_vertexIso _ q h) R hR
    (cocartesianStrictTransportScaffoldRestriction p q)
  · exact (cocartesianStrictTransportScaffoldRestriction_isPullback p q).w
  · intro x hx
    exact (cocartesianRelativeFunctorPredicate_iff_scaffold p q x).mp hx

/-- 同じ strict transport の全相対 Hom 作用は、元の写像空間の quasicategory の同値。 -/
@[kerodon 037V]
lemma cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C)
    [CocartesianFibration p] [CocartesianFibration q] :
    IsQCatEquivalence (cocartesianStrictTransportMappingSpaceMap p q) := by
  apply (cocartesianDiagramScaffoldMappingSpaceMap_isQCatEquivalence
    (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p) q).cancel_right
  rw [cocartesianStrictTransportMappingSpaceMap_scaffold]
  exact cocartesianStrictTransportScaffoldRestriction_isQCatEquivalence p q

end SerrePositivity.InfinityCategories
