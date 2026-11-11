module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitsIdempotentComplete
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteSubcomplexRetracts

/-!
概要：presentable な実 Ind 像は、元の射圏内の retract に閉じる。
方針：実像内の coherent 冪等分裂を、元の全部分圏の retract 回収へ渡す。
規約：両端点だけの retract ではなく、元の全射圏の retract を扱う。
使われ方：HTT 5.5.4.14 の実像の閉性を、二対三則の残りと独立に回収する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

omit [Fact μ.IsRegular] in
/-- 元の全射圏内の指定 retract は、同じ実像に戻る。 -/
lemma indArrowImageVertex_of_retract (edges : I → C _⦋1⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hI : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G))
    {f g : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G g) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G f := by
  let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G) _⦋0⦌ := ⟨g, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, Functor.map_id_apply]
    exact hg⟩
  obtain ⟨w, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retract_iso_in_complete_fullSubcomplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G) hI.hasSmallLimits.isIdempotentComplete z f r
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageVertex_iff_vertexIso edges G e).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex w)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
