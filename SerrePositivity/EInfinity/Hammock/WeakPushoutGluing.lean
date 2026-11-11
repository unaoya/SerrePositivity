module

public import SerrePositivity.EInfinity.Hammock.WeakUnderPushout

/-!
# 元の二つの pushout の比較の弱同値性

概要：同じ側が単射である二つの pushout の三成分の比較が弱同値なら残りも弱同値。
方針：元の基底の変更、固定境界の比較、単射に沿う pushout 保存を組み合わせる。
規約：元の比較射を扱い、その単射性や元の対象の Kan 性は仮定しない。
使われ方：proper 図式の境界の有限和と長さ段階の弱同値の貼り合わせ。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories

lemma weakPushout_gluing
    {A B C D A' B' C' D' : SSet.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} [Mono i] [Mono i']
    {g : A ⟶ C} {g' : A' ⟶ C'} {r : B ⟶ D} {s : C ⟶ D}
    {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (hP : IsPushout i g r s) (hP' : IsPushout i' g' r' s')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence b)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence c) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence d := by
  let M := pushout i a
  let u : B ⟶ M := pushout.inl i a
  let j : A' ⟶ M := pushout.inr i a
  have hM : IsPushout i a u j := IsPushout.of_hasPushout _ _
  have : Mono j := Adhesive.mono_of_isPushout_of_mono_left hM
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence u := weakPushout_other_mono ha hM.flip
  let β : M ⟶ B' := pushout.desc b i' hi
  have hβu : u ≫ β = b := pushout.inl_desc _ _ _
  have hβj : j ≫ β = i' := pushout.inr_desc _ _ _
  have hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence β := by
    apply hu.cancel_left
    rw [hβu]
    exact hb
  let N := pushout j g'
  let v : M ⟶ N := pushout.inl j g'
  let w : C' ⟶ N := pushout.inr j g'
  have hN : IsPushout j g' v w := IsPushout.of_hasPushout _ _
  let δ : N ⟶ D' := pushout.desc (β ≫ r') s' (by
    rw [← Category.assoc, hβj, hP'.w])
  have hδv : v ≫ δ = β ≫ r' := pushout.inl_desc _ _ _
  have hδw : w ≫ δ = s' := pushout.inr_desc _ _ _
  have hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence δ :=
    weakPushout_fixed_base hN hP' β δ hβj hδv hδw hβ
  have hglue : i ≫ (u ≫ v) = g ≫ (c ≫ w) := by
    rw [← Category.assoc, hM.w, Category.assoc, hN.w, ← Category.assoc, ← hg, Category.assoc]
  let γ : D ⟶ N := hP.desc (u ≫ v) (c ≫ w) hglue
  have hγr : r ≫ γ = u ≫ v := hP.inl_desc _ _ _
  have hγs : s ≫ γ = c ≫ w := hP.inr_desc _ _ _
  have hOuter : IsPushout i (g ≫ c) (u ≫ v) w := by
    rw [hg]
    exact hM.paste_vert hN
  have hOuter' : IsPushout i (g ≫ c) (r ≫ γ) w := by
    rw [hγr]
    exact hOuter
  have hγP : IsPushout s c γ w := hOuter'.of_top hγs hP
  have : Mono s := Adhesive.mono_of_isPushout_of_mono_left hP
  have hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence γ := weakPushout_other_mono hc hγP.flip
  have hcomp : γ ≫ δ = d := by
    apply hP.hom_ext
    · rw [← Category.assoc, hγr, Category.assoc, hδv, ← Category.assoc, hβu, hr]
    · rw [← Category.assoc, hγs, Category.assoc, hδw, hs]
  rw [← hcomp]
  exact hγ.comp hδ


end SerrePositivity.EInfinity.Hammock
