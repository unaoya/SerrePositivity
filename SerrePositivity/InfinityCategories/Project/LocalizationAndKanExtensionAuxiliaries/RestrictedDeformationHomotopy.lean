module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FullSubcomplexHomotopyLift
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyPrecompVertex
/-!
概要：変形比較を、包含の像を含む頂点全部分圏上の同じ実比較へ制限する。
方針：元のホモトピーを全部分圏から引き戻し、両端をその全部分圏へ持ち上げる。
規約：辺や分解の選択を変えない。使われ方：K-flat 加群上の局所化。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
/-- 包含の像を含む頂点全部分圏上にも、元の同じ変形比較が持ち上がる。 -/
def deformationRestrictedHomotopy {X D : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (L : X ⟶ D) (I : D ⟶ X)
    (hI : ∀ x, P (I.app (Opposite.op ⦋0⦌) x))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X)) :
    SSet.Homotopy
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P I hI)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet)) := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P I hI
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H K.ι
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.fullSubcomplexHomotopyLift P
  exact { h := H'.h
          h₀ := by
            simpa only [K, J, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using! H'.h₀
          h₁ := by
            simpa only [Category.comp_id, Category.id_comp] using! H'.h₁
          rel := H'.rel }
/-- 制限した比較の頂点辺は、元の同じ頂点での実辺そのもの。 -/
lemma deformationRestrictedHomotopy_vertex_val {X D : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (L : X ⟶ D) (I : D ⟶ X)
    (hI : ∀ x, P (I.app (Opposite.op ⦋0⦌) x))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (deformationRestrictedHomotopy P L I hI H) x).edge.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x.val).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) x).edge = _
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge H _ x
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
