module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberIntervalIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalVertexHomotopy

/-!
概要：同じ標的を持つ comma の矢印の Hom 類による始対象性の不変性。
方針：二重 fiber の区間模型の同型を使い、元の二単体からの頂点同型を戻す。
規約：標的は同じ Y 内の頂点として固定。単位の代表の厳密な一致は要求しない。
使われ方：元の coherent な comma 切断と単位の選び直した代表の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ元の標的を固定した comma の点が表す、元の端点を持つ辺。 -/
def commaTargetFiberArrow {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (v : (vertexFiber (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y) _⦋0⦌) :
    X.Edge x (G.app (Opposite.op ⦋0⦌) y) :=
  intervalMappingEdgeOfVertex ((SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval G x y).app _ v)

/-- 単体集合の同型で写した頂点間の同型を、元の二頂点間へ戻す。 -/
def vertexIsoOfSimplicialIsoImage {A B : SSet.{u}} (e : A ≅ B) (v w : A _⦋0⦌)
    (i : VertexIso (X := B) (e.hom.app (Opposite.op ⦋0⦌) v)
      (e.hom.app (Opposite.op ⦋0⦌) w)) : VertexIso (X := A) v w := by
  have hv : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) v) = v :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) v
  have hw : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) w) = w :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) w
  exact eqToIso (congrArg HomotopyCategory.mk hv.symm) ≪≫ i.map e.inv ≪≫
    eqToIso (congrArg HomotopyCategory.mk hw)

/-- 同じ標的上で同じ Hom 類を表す comma の二点は、元の始域 fiber 内で同型。 -/
def unitCommaTargetFiberVertexIsoOfHomMkEq {X Y : SSet.{u}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (v w : (vertexFiber (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y) _⦋0⦌)
    (h : Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x y v).toTruncated =
      Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x y w).toTruncated) :
    VertexIso (X := unitCommaFiber G x) v.val w.val := by
  let e := SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso G x y
  let i := intervalVertexIsoOfRecoveredHomMkEq
    ((SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval G x y).app _ v)
    ((SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval G x y).app _ w) h
  exact (vertexIsoOfSimplicialIsoImage e v w i).map
    (vertexFiberι (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y)

/-- 元の標的と矢印の Hom 類を保つ代表の変更は、comma の始対象性を保持。 -/
lemma unitCommaTargetFiber_isInitial_iff_of_homMk_eq {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (v w : (vertexFiber (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y) _⦋0⦌)
    (h : Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x y v).toTruncated =
      Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x y w).toTruncated) :
    IsInitialVertex v.val ↔ IsInitialVertex w.val := by
  have : Quasicategory (unitCommaFiber G x) :=
    quasicategory_of_innerFibration (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x)
  exact isInitialVertex_iff_of_vertexIso (unitCommaTargetFiberVertexIsoOfHomMkEq G x y v w h)

end SerrePositivity.InfinityCategories.HomotopyLimits
