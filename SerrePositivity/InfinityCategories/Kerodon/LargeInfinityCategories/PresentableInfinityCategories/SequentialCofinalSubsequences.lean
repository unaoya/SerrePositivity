module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction

/-!
概要：可算交互列の偶数・奇数部分列は、元の全列と同じ余極限を計算する。
方針：単調で上に共終な自然数列の右 comma に最小の始対象を作る。
規約：通常の final 性だけでなく元の nerve の right cofinal 性を使う。
使われ方：二成分の表示を同期する全交互列の部分余極限比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定した単調自然数列を、小さい持ち上げた順序圏の関手として読む。
方針：対象と不等式を同時に持ち上げる。
規約：宇宙 u の小さい添字を使う。
使われ方：偶数・奇数部分列の全 nerve 写像。 -/
def sequentialSubsequenceFunctor (a : ℕ → ℕ) (ha : Monotone a) :
    ULift.{u} ℕ ⥤ ULift.{u} ℕ :=
  (show Monotone (fun n : ULift.{u} ℕ ↦ ULift.up (a n.down)) from
    fun _ _ h ↦ ha h).functor

/-- 概要：上に共終な単調自然数列は、同じ nerve の right cofinal 写像を与える。
方針：各右 comma の対象として最初に指定値を越える項を取り、始対象性を示す。
規約：可算列全体の全高次の cofinal 性を結論する。
使われ方：同期列の任意の共終部分列の余極限計算。 -/
lemma sequentialSubsequence_nerve_isRightCofinal (a : ℕ → ℕ) (ha : Monotone a)
    (hcofinal : ∀ k, ∃ n, k ≤ a n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (sequentialSubsequenceFunctor.{u} a ha)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
  intro k
  let n := Nat.find (hcofinal k.down)
  let f : k ⟶ (sequentialSubsequenceFunctor.{u} a ha).obj (ULift.up n) :=
    homOfLE (Nat.find_spec (hcofinal k.down))
  refine ⟨StructuredArrow.mk f, ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · have hy₀ : k ≤ (sequentialSubsequenceFunctor.{u} a ha).obj y.right := leOfHom y.hom
    have hy : k.down ≤ a y.right.down := hy₀
    have hn : (ULift.up n : ULift.{u} ℕ) ≤ y.right := Nat.find_min' (hcofinal k.down) hy
    exact StructuredArrow.homMk (homOfLE hn) (by subsingleton)
  · intro y g
    apply StructuredArrow.hom_ext
    exact Subsingleton.elim _ _

/-- 概要：偶数列・奇数列を含む、二倍して固定値を加えた部分列は right cofinal。
方針：単調性と上への共終性を自然数の不等式で確認する。
規約：offset 0 と 1 が偶数列と奇数列である。
使われ方：交互列の二成分の余極限の比較。 -/
lemma doubleSubsequence_nerve_isRightCofinal (offset : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (sequentialSubsequenceFunctor.{u}
      (fun n ↦ 2 * n + offset)
        (by intro m n h; change 2 * m + offset ≤ 2 * n + offset; omega))) :=
  sequentialSubsequence_nerve_isRightCofinal _ _ (fun k ↦ ⟨k, by omega⟩)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
