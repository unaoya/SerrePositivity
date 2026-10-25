module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSeedBounds
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSuccessorDiagram

/-!
概要：元の poset 表示内の後続因子化は、旧端点より後にあることを証明する。
方針：元の全添字余錐の脚を nerve の実際の順序射に戻す。
規約：表示の添字を別の poset に変更しない。使われ方：交互列の両側の単調性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- poset 内の全余錐の各脚は、元の同じ poset 内の不等式を与える。 -/
lemma nerve_cocone_le {A : Type u} [Preorder A] {K : SSet.{u}}
    (q : K ⟶ nerve A) (c : JoinCocone q) (t : K _⦋0⦌) :
    nerveEquiv (q.app _ t) ≤ nerveEquiv c.vertex := by
  let l := c.leg (SSet.yonedaEquiv.symm t)
  have hs : SSet.yonedaEquiv (SSet.yonedaEquiv.symm t ≫ q) = q.app _ t := by
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  let e : (nerve A).Edge (q.app _ t) c.vertex := ⟨l.edge, l.src_eq.trans hs, l.tgt_eq⟩
  exact leOfHom (CategoryTheory.nerve.homEquiv e)

/-- 左側の後続として選んだ添字は、旧全前置図式の全頂点を支配する。 -/
lemma ComparisonLeftFactor.index_ge {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {A : Type u} [Preorder A] {I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
    {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁} (f : ComparisonLeftFactor s)
    (t : s.left_shape _⦋0⦌) :
    nerveEquiv (s.left_index.app _ t) ≤
      nerveEquiv (JoinCocone.vertex (p := s.left_index) f.index) :=
  nerve_cocone_le s.left_index f.index t

/-- とくに左側の旧終端点は、元の同じ poset 内の次の終端点以下である。 -/
lemma ComparisonLeftFactor.terminal_index_le {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {A : Type u} [Preorder A] {I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
    {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁} (f : ComparisonLeftFactor s) :
    nerveEquiv (s.left_index.app _ s.left_terminal) ≤
      nerveEquiv (JoinCocone.vertex (p := s.left_index) f.index) :=
  f.index_ge s.left_terminal

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
