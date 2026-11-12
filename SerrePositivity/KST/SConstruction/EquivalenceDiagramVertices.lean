module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagrams

/-! # 全同値図式の対象と core への図式
概要：全同値図式の圏の対象は、添字から core への射と厳密に対応する。
方針：core の全辺の普遍条件と内部 Hom の頂点同値を合わせる。
規約：図式間の自然変換を core の射に置換しない。使われ方：object/core の行の対応。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：core への図式を全同値図式の圏の頂点にする。
方針：包含後の全辺の可逆性を core の辺の定理から得る。
規約：標的の quasicategory 性は不要。使われ方：対象の対応の逆向き。 -/
def equivalenceDiagramVertexOfCoreMap {K C : SSet.{u}} (F : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u})) :
    (equivalenceDiagrams K C) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    apply (isEquivalenceDiagramVertex_functorVertex _).2
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (F.app (Opposite.op ⦋1⦌) s)⟩

/-- 概要：全同値図式の圏の頂点を core への実際の図式へ持ち上げる。
方針：頂点の全辺の可逆性を core の普遍的な持ち上げへ渡す。
規約：全ての高次単体を持つ射を返す。使われ方：対象の対応の順向き。 -/
def equivalenceDiagramCoreMap {K C : SSet.{u}} (v : (equivalenceDiagrams K C) _⦋0⦌) :
    K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm v.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)

/-- 概要：全同値図式の対象は core への図式と同値。
方針：core の包含の単射性と関手頂点の同値の逆律。
規約：周囲の自然変換まで core に制限した同型ではない。使われ方：object/core 比較の行の単体。 -/
def equivalenceDiagramVerticesEquiv (K C : SSet.{u}) :
    (equivalenceDiagrams K C) _⦋0⦌ ≃ (K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u})) where
  toFun := equivalenceDiagramCoreMap
  invFun := equivalenceDiagramVertexOfCoreMap
  left_inv v := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (equivalenceDiagramCoreMap v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι) = v.val
    rw [equivalenceDiagramCoreMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).apply_symm_apply _
  right_inv F := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι).1
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι)) = _
    exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.SConstruction
