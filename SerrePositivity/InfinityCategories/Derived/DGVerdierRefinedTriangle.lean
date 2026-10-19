module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedApex
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexTriangleApexLift

/-! # 閉細分した実図式辺の三角形を実分母 over へ持ち上げる

概要：追加閉分母後の実四面体から、元の図式辺を保つ実分母部分圏内の二単体を構成する。
方針：回収 over 三角形の新始頂点と零面の分母条件を使い、同じ二単体を全部分複体へ上げる。
規約：全ての細分データと指定辺を保持。使われ方：有限共通始錐の辺上の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 指定図式辺を保ち、追加実閉分母後の同じ三角形を実分母 over へ持ち上げる。 -/
def dgVerdierDiagramRefinedTriangle (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s) :
    (dgVerdierOver A D P x : SSet.{max u v}) _⦋2⦌ :=
  fullSubcomplexTriangleApexLift (IsDGVerdierOverVertex A D P x)
    (dgVerdierDiagramRefinedOverTriangle A D C e q s F hF) (f.app _ e)
    (dgVerdierDiagramRefinedOverTriangle_face0 A D C e q s F hF)
    (dgVerdierDiagramRefinedApex_mem A D C e q s hs F hF)

/-- 実分母部分圏への持ち上げは、同じ四面体から回収した over 二単体の台を保つ。 -/
lemma dgVerdierDiagramRefinedTriangle_val (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s) :
    (dgVerdierDiagramRefinedTriangle A D C e q s hs F hF).val =
      dgVerdierDiagramRefinedOverTriangle A D C e q s F hF := rfl

/-- 持ち上げた実分母三角形の零面は、元の指定実図式辺そのもの。 -/
lemma dgVerdierDiagramRefinedTriangle_face0 (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s) :
    (dgVerdierOver A D P x : SSet.{max u v}).δ 0
      (dgVerdierDiagramRefinedTriangle A D C e q s hs F hF) = f.app _ e :=
  fullSubcomplexTriangleApexLift_face0 (IsDGVerdierOverVertex A D P x) _ _ _ _

end SerrePositivity.InfinityCategories
