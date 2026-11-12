module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierNormalizeTriangleCones

/-! # 二次まで面・退化を保つ実分母図式の共通始錐

概要：同じ頂点錐・全辺錐・全二単体の実三単体を、全ての面と退化の厳密式で束ねる。
方針：有限二単体を一度だけ列挙して充填し、標準退化による正規化を適用する。
規約：三次以上の整合性を含めない。使われ方：高次の有限共通始錐の帰納の基礎。
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

/-- 実分母図式の、二次まで全ての面・基本退化と厳密に整合する共通始錐データ。 -/
structure DGVerdierDiagramTwoCone (P : Set D) (x : D) {K : SSet.{max u v}}
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) where
  vertexCone : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f
  edgeCone (e : K _⦋1⦌) : Truncated.Edge.CompStruct
    (vertexCone.leg (K.δ 1 e)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f))
    (vertexCone.leg (K.δ 0 e))
  edge_unit (v : K _⦋0⦌) : (edgeCone (K.σ 0 v)).simplex =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (vertexCone.leg v).edge
  triangleCone : K _⦋2⦌ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌
  triangle_face0 (σ : K _⦋2⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (triangleCone σ) = f.app _ σ
  triangle_face_cone (σ : K _⦋2⦌) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ (triangleCone σ) = (edgeCone (K.δ i σ)).simplex
  triangle_degeneracy (i : Fin 2) (e : K _⦋1⦌) :
    triangleCone (K.σ i e) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ i.succ (edgeCone e).simplex

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 二次まで有限な実分母図式には、二次まで面・退化を保つ共通始錐が存在する。 -/
theorem dgVerdierDiagramTwoCone_nonempty (P : Set D) (x : D) {K : SSet.{max u v}}
    [Finite (K _⦋0⦌)] [Finite (K _⦋1⦌)] [Finite (K _⦋2⦌)]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) :
    Nonempty (DGVerdierDiagramTwoCone A D P x f) := by
  classical
  let : Fintype (K _⦋2⦌) := Fintype.ofFinite _
  let ε := Fintype.equivFin (K _⦋2⦌)
  obtain ⟨C, H, U, hunit, hU⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramFiniteTriangles_exists_unitalVertexCone A D P x f ε.symm
  let F (σ : K _⦋2⦌) := U (ε σ)
  have hF (σ : K _⦋2⦌) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H σ (F σ) := by
    have h := hU (ε σ)
    rw [ε.symm_apply_apply] at h
    exact h
  let V := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierNormalizeTriangleCone A D C H F
  have hV (σ : K _⦋2⦌) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H σ (V σ) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierNormalizeTriangleCone_boundary A D C H F hunit hF σ
  exact ⟨{
    vertexCone := C
    edgeCone := H
    edge_unit := hunit
    triangleCone := V
    triangle_face0 := fun σ => (hV σ).1
    triangle_face_cone := fun σ => (hV σ).2
    triangle_degeneracy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierNormalizeTriangleCone_degeneracy A D C H F hunit }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
