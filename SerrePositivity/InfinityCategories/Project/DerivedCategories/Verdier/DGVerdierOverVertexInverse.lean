module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverVertexInverse

/-! # 実 Verdier over 頂点の指定厳密分母表示

概要：実 Verdier over 頂点から元の閉分母を回収し、屋根比較の零単体上の全射性を得る。
方針：回収した実辺の厳密一致から分母条件を移し、全部分型の外延性で頂点を照合する。
規約：零次元の全射性から cofinality を推論しない。使われ方：実屋根添字との比較。
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

/-- 実分母 over の零単体の台は、指定分母条件を満たす。 -/
lemma dgVerdierOverVertex_mem (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x σ.val := by
  simpa only [op_id, Functor.map_id_apply] using σ.property (𝟙 ⦋0⦌)

/-- 実 Verdier over 頂点を、同じ実辺を持つ元の厳密閉分母として表示する。 -/
def dgVerdierOverVertexClosed (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexClosed A D x σ.val, by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexClosed A D x σ.val).hom).edge ∈ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexClosed_edge]
    exact dgVerdierOverVertex_mem A D P x σ⟩

/-- 実分母から回収した指定厳密分母は、同じ実 over 頂点を与える。 -/
lemma dgVerdierOverVertexClosed_vertex (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x (dgVerdierOverVertexClosed A D P x σ) = σ := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexClosed_vertex A D x σ.val

/-- 厳密屋根比較の零単体上の明示的な右逆。 -/
lemma dgClosedRoofVerdierMap_vertex_rightInverse (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (dgVerdierOverVertexClosed A D P x σ)) = σ := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_vertex A D P x _).trans
    (dgVerdierOverVertexClosed_vertex A D P x σ)

/-- 厳密屋根 nerve から実 Verdier over 圏への比較は零単体上全射。 -/
lemma dgClosedRoofVerdierMap_vertex_surjective (P : Set D) (x : D) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋0⦌)) := by
  intro σ
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (dgVerdierOverVertexClosed A D P x σ),
    dgClosedRoofVerdierMap_vertex_rightInverse A D P x σ⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
