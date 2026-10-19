module
public import SerrePositivity.InfinityCategories.Derived.DGOverTwoSimplexInitialApex
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexTriangleApexLift

/-! # 実分母 over 二単体の同じ閉始点細分

概要：任意の実分母 over 二単体を、同じ追加閉分母で細分した実分母二単体へ戻す。
方針：始頂点の合成分母性と元の零面の所属を使い、回収した同じ台を持ち上げる。
規約：元の零面と細分四面体を厳密に保持。使われ方：有限高次図式の共通辺錐。
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
variable [Small.{u} D] [IsDGPretriangulated A D]
variable (P : Set D) (x : D)
variable (σ : (dgVerdierOver A D P x : SSet.{max u v}) _⦋2⦌) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  (((SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron _ σ.val)).obj 0))
variable (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)

/-- 元の零面を保つ、同じ追加閉分母による実分母二単体の始点細分。 -/
def dgVerdierTwoSimplexInitialRefinement : (dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  fullSubcomplexTriangleApexLift (IsDGVerdierOverVertex A D P x)
    (dgOverTwoSimplexInitialRefinement A D x σ.val q s) ((dgVerdierOver A D P x : SSet).δ 0 σ)
    (dgOverTwoSimplexInitialRefinement_face0 A D x σ.val q s)
    (dgOverTwoSimplexInitialRefinement_apex_mem A D x σ.val q s P
      (fullSubcomplexOnVertices_vertex
        ((dgVerdierOver A D P x : SSet).δ 1 ((dgVerdierOver A D P x : SSet).δ 1 σ))) hs)

/-- 実分母二単体の細分は、回収した同じ over 二単体の台を保持する。 -/
lemma dgVerdierTwoSimplexInitialRefinement_val :
    (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs).val =
      dgOverTwoSimplexInitialRefinement A D x σ.val q s := rfl

/-- 同じ細分の回収四面体は、元の回収四面体の一般閉始点細分。 -/
lemma dgVerdierTwoSimplexInitialRefinement_tetrahedron :
    roofPointSliceTetrahedron _ (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs).val =
      dgOverTwoSimplexInitialTetrahedron A D x σ.val q s :=
  dgOverTwoSimplexInitialRefinement_tetrahedron A D x σ.val q s

/-- 実分母部分圏内でも、細分後の零面は元の指定零面のまま。 -/
lemma dgVerdierTwoSimplexInitialRefinement_face0 :
    (dgVerdierOver A D P x : SSet).δ 0
      (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs) =
        (dgVerdierOver A D P x : SSet).δ 0 σ :=
  Subtype.ext (dgOverTwoSimplexInitialRefinement_face0 A D x σ.val q s)

end SerrePositivity.InfinityCategories
