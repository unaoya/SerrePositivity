module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierInitialDiagonal

/-! # 実図式辺ホーンの共通始対象と指定終対象

概要：各実図式辺から回収した始対象は元の共通閉分母の始対象で、終対象は指定 x である。
方針：元の対角辺 03 を共通始頂点の指定閉分母辺と厳密に同定し、両端点を評価する。
規約：全図式辺で同じ共通始対象。使われ方：有限同時原始元の共通始域への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 各図式辺ホーンの元の対角 03 は、同じ共通閉分母の実辺。 -/
lemma dgVerdierDiagramInitialDiagonal_edge :
    (dgNerve A D).δ 1 (dgLastHornCanonicalFace
      (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)) =
      (dgClosedEdge A D C.denominator.obj.hom).edge :=
  (dgVerdierConeInitialDiagonal_edge A D P x (C.leg (K.δ 1 e))
    ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))).trans
      (dgClosedOverVertex_edge A D C.denominator.obj.hom)

/-- 各実図式辺ホーンの回収始対象は、元の同じ共通閉分母の始対象。 -/
lemma dgVerdierDiagramHorn_source :
    (HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0 =
      ForgetEnrichment.to (Complex A) C.denominator.obj.left :=
  congrArg (fun t : Simplex A D 1 => t.obj 0) (dgVerdierDiagramInitialDiagonal_edge A D C e)

/-- 各実図式辺ホーンの回収終対象は、元の指定終対象 x。 -/
lemma dgVerdierDiagramHorn_target :
    (HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 3 = x :=
  congrArg (fun t : Simplex A D 1 => t.obj 1) (dgVerdierDiagramInitialDiagonal_edge A D C e)

end SerrePositivity.InfinityCategories
