module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FullSubcomplexVertexExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinVertexSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：全部分複体の指定頂点の始対象性を周囲から反映する。
方針：周囲の境界の充填を、全頂点を含む同じ境界から全部分複体へ戻す。
使われ方：HTT §1.2.12、Kerodon Proposition 4.7.3.11（Tag 06R1）の始対象の境界判定。
規約：指定頂点と境界を変えない。準圏性は不要。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 周囲で始対象である全部分複体の頂点は、内部でも同じ始対象である。 -/
lemma fullSubcomplexOnVertices_isInitialVertex_of_image {X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (hx : IsInitialVertex x.val) : IsInitialVertex x := by
  intro n b hb
  let i := (fullSubcomplexOnVertices X P).ι
  have hb' : boundaryVertex n 0 ≫ (b ≫ i) = SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n (b ≫ i) hb'
  obtain ⟨L, hL, _⟩ := fullSubcomplex_vertex_extension P _
    (boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
