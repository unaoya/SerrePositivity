module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverTwoSimplexInitialApex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.FullSubcomplexTriangleApexLift

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D)
variable (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋2⦌) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  (((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ.val)).obj 0))
variable (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)

/-- 元の零面を保つ、同じ追加閉分母による実分母二単体の始点細分。 -/
def dgVerdierTwoSimplexInitialRefinement : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexTriangleApexLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ.val q s) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_face0 A D x σ.val q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_apex_mem A D x σ.val q s P
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 σ))) hs)

/-- 実分母二単体の細分は、回収した同じ over 二単体の台を保持する。 -/
lemma dgVerdierTwoSimplexInitialRefinement_val :
    (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x σ.val q s := rfl

/-- 同じ細分の回収四面体は、元の回収四面体の一般閉始点細分。 -/
lemma dgVerdierTwoSimplexInitialRefinement_tetrahedron :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialTetrahedron A D x σ.val q s :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_tetrahedron A D x σ.val q s

/-- 実分母部分圏内でも、細分後の零面は元の指定零面のまま。 -/
lemma dgVerdierTwoSimplexInitialRefinement_face0 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
      (dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 σ :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_face0 A D x σ.val q s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
