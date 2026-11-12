module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEquiv

/-!
概要：通常の圏の nerve への射を一次単体上の値で判定する。
方針：正次元は strict Segal の単射性、零次元は退化辺で判定する。
規約：始域は任意の単体集合を許す。
使われ方：B5 の標準錐と通常の錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：nerve への二つの射は全一次単体で等しければ等しい。
方針：切り詰めた nerve の strict Segal 性を全次数に適用する。
規約：同じ宇宙の小さい圏と任意の始域を扱う。
使われ方：B5 の標準錐の高次成分の同定。 -/
lemma nerve_hom_ext_one {X : SSet.{u}} {C : Type u} [Category.{u} C] {f g : X ⟶ nerve C}
    (h : ∀ s : X _⦋1⦌, f.app _ s = g.app _ s) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  cases n with
  | zero =>
    have he := h (X.σ 0 s)
    change f.app _ (X.map (SimplexCategory.σ 0).op s) =
      g.app _ (X.map (SimplexCategory.σ 0).op s) at he
    rw [f.naturality_apply, g.naturality_apply] at he
    exact ComposableArrows.ext₀ (congrArg (fun t : ComposableArrows C 1 ↦ t.obj 0) he)
  | succ n =>
    apply SSet.Truncated.IsStrictSegal.ext (X := (truncation (n + 1)).obj (nerve C))
      (hd := by simp)
    intro i
    change (nerve C).map (SimplexCategory.mkOfSucc i).op (f.app _ s) =
      (nerve C).map (SimplexCategory.mkOfSucc i).op (g.app _ s)
    rw [← f.naturality_apply, ← g.naturality_apply]
    exact h _

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
