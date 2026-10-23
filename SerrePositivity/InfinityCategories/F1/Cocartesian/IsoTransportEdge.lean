module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportFamily
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedComparisonInvertible

/-!
概要：全局所 Hom の同型比較を、元の分類主写像の間の同じ可逆辺にする。
方針：元の区間族を転置し、既存の両端公式と成分同値性を使う。
規約：始域評価・結合共役と元の分類主写像を保持する。
使われ方：全局所比較の同じ可逆 path の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (A : Type u) [Category.{u} A]

/-- 元の全局所 Hom の比較を表す、同じ区間族。 -/
def cocartesianIsoTransportIntervalFamily :
    CocartesianIsoTransportInfinity A ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  cocartesianIsoTransportFamily A ≫ qCatDiagramArrowCurry A

/-- 同じ区間族の零端点は、元の始域評価に続く同じ分類。 -/
lemma cocartesianIsoTransportIntervalFamily_zero :
    cocartesianIsoTransportIntervalFamily A ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    cocartesianIsoTransportSource A ≫ cocartesianStraighteningCoherentMap A := by
  rw [cocartesianIsoTransportIntervalFamily, Category.assoc,
    qCatDiagramArrowCurry_endpoint]
  exact cocartesianIsoTransportFamily_zero A

/-- 同じ区間族の一端点は、元の結合共役に続く同じ分類。 -/
lemma cocartesianIsoTransportIntervalFamily_one :
    cocartesianIsoTransportIntervalFamily A ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    cocartesianIsoTransportTarget A ≫ cocartesianStraighteningCoherentMap A := by
  rw [cocartesianIsoTransportIntervalFamily, Category.assoc,
    qCatDiagramArrowCurry_endpoint]
  exact cocartesianIsoTransportFamily_one A

/-- 端点を正規化する前の、元の全局所区間族の可逆性。 -/
lemma cocartesianIsoTransportIntervalFamily_isInvertible :
    IsInvertibleEdge (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A))).toTruncated) := by
  exact QuasicategoryEnrichedDiagramComparison.interval_isInvertible
    (C := IsoTransportObject (CocartesianFibrationObject (nerve A)))
    (J := A)
    (D := (cocartesianStrictTransportEnrichedDiagram A).precompose
      (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A))))
    (E := (cocartesianStrictTransportEnrichedDiagram A).precompose
      (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A))))
    (cocartesianIsoTransportDiagramComparison A)
    (fun a X ↦ isoTransportQuasicategoryDiagramComparison_component_isQCatEquivalence
      (cocartesianStrictTransportEnrichedDiagram A) a X)

/-- 元の始域評価と結合共役の分類像の間の、同じ全局所比較の辺。 -/
def cocartesianIsoTransportEdge :
    Edge (functorVertex (cocartesianIsoTransportSource A ≫
      cocartesianStraighteningCoherentMap A))
      (functorVertex (cocartesianIsoTransportTarget A ≫
        cocartesianStraighteningCoherentMap A)) :=
  ((SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A))).ofEq
    (by rw [transposeFunctorFamily_vertex, cocartesianIsoTransportIntervalFamily_zero])
    (by rw [transposeFunctorFamily_vertex, cocartesianIsoTransportIntervalFamily_one])

/-- 同じ全局所比較の辺は、元の各同型の関手像として可逆。 -/
lemma cocartesianIsoTransportEdge_isInvertible :
    IsInvertibleEdge (cocartesianIsoTransportEdge A).toTruncated := by
  unfold cocartesianIsoTransportEdge
  exact isInvertibleEdge_ofEq _ _ _ (cocartesianIsoTransportIntervalFamily_isInvertible A)

end SerrePositivity.InfinityCategories
