module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitsIdempotentComplete
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteSubcomplexRetracts

/-!
概要：presentable な実 Ind 像は、元の射圏内の retract に閉じる。
方針：実像内の coherent 冪等分裂を、元の全部分圏の retract 回収へ渡す。
規約：両端点だけの retract ではなく、元の全射圏の retract を扱う。
使われ方：HTT 5.5.4.14 の実像の閉性を、二対三則の残りと独立に回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

omit [Fact μ.IsRegular] in
/-- 元の全射圏内の指定 retract は、同じ実像に戻る。 -/
lemma indArrowImageVertex_of_retract (edges : I → C _⦋1⦌)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hI : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (indArrowImageCategory edges G))
    {f g : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hg : IndArrowImageVertex edges G g) (r : Idempotent.VertexRetraction f g) :
    IndArrowImageVertex edges G f := by
  let z : (indArrowImageCategory edges G) _⦋0⦌ := ⟨g, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, Functor.map_id_apply]
    exact hg⟩
  obtain ⟨w, ⟨e⟩⟩ := Idempotent.retract_iso_in_complete_fullSubcomplex
    (IndArrowImageVertex edges G) hI.hasSmallLimits.isIdempotentComplete z f r
  exact (indArrowImageVertex_iff_vertexIso edges G e).mpr
    (fullSubcomplexOnVertices_vertex w)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
