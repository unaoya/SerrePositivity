module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionNaturality
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 一つの入力への代入とテンソル単位

概要：Berger–Moerdijk §1 の単位則を、最後の入力から定義した反復代入に接続する。
方針：残りの内側演算族が空のときの交換と単位子を簡約する。
規約：テンソル単位との Koszul 交換には既存の対称性の単位則を用いる。
使われ方：全入力への合成の一次の場合と自由代数の単位作用の証明に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：残りの演算族が空なら有限族の代入は一つの係数射の適用になる（Berger–Moerdijk §1）。
方針：空の族との交換を相殺し、右単位子の自然性とモノイダル整合性を使う。
規約：一次の有限テンソルに付く最後のテンソル単位を右単位子で除く。
使われ方：反復代入の一次の場合を通常の部分合成へ簡約する。 -/
lemma tensorFamilySubstitutionStep_zero {R R' : Complex A} (V : Fin 1 → Complex A)
    (f : R ⊗ V (Fin.last 0) ⟶ R') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep 0 V f (ρ_ R').hom = (R ◁ (ρ_ (V 0)).hom) ≫ f := by
  change R ⊗ V 0 ⟶ R' at f
  have hs : (ρ_ (V 0)).hom ≫ (λ_ (V 0)).inv ≫
      (β_ (𝟙_ (Complex A)) (V 0)).hom = 𝟙 (V 0 ⊗ 𝟙_ (Complex A)) := by
    rw [leftUnitor_inv_braiding]
    exact Iso.hom_inv_id _
  have hs' : (R ◁ ((ρ_ (V 0)).hom ≫ (λ_ (V 0)).inv)) ≫
      (R ◁ (β_ (𝟙_ (Complex A)) (V 0)).hom) = 𝟙 (R ⊗ (V 0 ⊗ 𝟙_ (Complex A))) := by
    rw [← whiskerLeft_comp, Category.assoc, hs, whiskerLeft_id]
  change (R ◁ ((ρ_ (V 0)).hom ≫ (λ_ (V 0)).inv)) ≫
    (R ◁ (β_ (𝟙_ (Complex A)) (V 0)).hom) ≫ (α_ R (V 0) (𝟙_ (Complex A))).inv ≫
      (f ▷ 𝟙_ (Complex A)) ≫ (ρ_ R').hom = _
  rw [← Category.assoc _ _ ((α_ R (V 0) (𝟙_ (Complex A))).inv ≫
    (f ▷ 𝟙_ (Complex A)) ≫ (ρ_ R').hom), hs', Category.id_comp,
      rightUnitor_naturality]
  have hc : (α_ R (V 0) (𝟙_ (Complex A))).inv ≫ (ρ_ (R ⊗ V 0)).hom =
      R ◁ (ρ_ (V 0)).hom := by monoidal_coherence
  rw [← Category.assoc, hc]

/-- 概要：一次の有限族の代入は右単位子の後の射の合成を保つ（Berger–Moerdijk §1）。
方針：空の残りの演算族の簡約の後に指定の射を合成する。
規約：係数射の終域の後の射は任意。
使われ方：反復合成の arity の移送を一次の部分合成の末尾へまとめる。 -/
lemma tensorFamilySubstitutionStep_zero_post {R R' O : Complex A} (V : Fin 1 → Complex A)
    (f : R ⊗ V (Fin.last 0) ⟶ R') (h : R' ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep 0 V f ((ρ_ R').hom ≫ h) =
      (R ◁ (ρ_ (V 0)).hom) ≫ f ≫ h := by
  have ht := congrArg (· ≫ h) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_zero V f)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, Category.assoc] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
