module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionMonoCobaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単射を含む二つの pushout の間の比較による前合成の同値条件。
方針：基底の変更を一度 pushout し、固定基底の比較と単射に沿う保存を合成する。
規約：各 pushout で同じ側の射が単射であることを要求する。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、Lemma 4.6.2.10（Tag 01HX） のセルによる比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射を含む二つの pushout の三つの対象間の比較が同値条件を満たせば第四の比較も満たす。
方針：基底の変更を B 側へ pushout した中間図式を挟み、固定基底と単射に沿う比較を使う。
規約：i、i' は単射。比較射 a、b、c と残りの貼り合わせ射に単射性は不要。
使われ方：Kerodon Proposition 4.5.5.9（Tag 01FB）、Lemma 4.6.2.10（Tag 01HX） の貼り合わせ。 -/
@[kerodon 0345]
lemma isPrecompositionEquivalence_of_pushout_gluing
    {A B C D A' B' C' D' : SSet.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} [Mono i] [Mono i']
    {g : A ⟶ C} {g' : A' ⟶ C'} {r : B ⟶ D} {s : C ⟶ D}
    {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (hP : IsPushout i g r s) (hP' : IsPushout i' g' r' s')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence c) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence d := by
  let M := pushout i a
  let u : B ⟶ M := pushout.inl i a
  let j : A' ⟶ M := pushout.inr i a
  have hM : IsPushout i a u j := IsPushout.of_hasPushout _ _
  have : Mono j := Adhesive.mono_of_isPushout_of_mono_left hM
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence u := ha.of_isPushout_of_mono_other hM.flip
  let β : M ⟶ B' := pushout.desc b i' hi
  have hβu : u ≫ β = b := pushout.inl_desc _ _ _
  have hβj : j ≫ β = i' := pushout.inr_desc _ _ _
  have hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence β := by
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
  have hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence δ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_pushout_fixed_base hN hP' β δ hβj hδv hδw hβ
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
  have hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence γ := hc.of_isPushout_of_mono_other hγP.flip
  have hcomp : γ ≫ δ = d := by
    apply hP.hom_ext
    · rw [← Category.assoc, hγr, Category.assoc, hδv, ← Category.assoc, hβu, hr]
    · rw [← Category.assoc, hγs, Category.assoc, hδw, hs]
  rw [← hcomp]
  exact hγ.comp hδ

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
