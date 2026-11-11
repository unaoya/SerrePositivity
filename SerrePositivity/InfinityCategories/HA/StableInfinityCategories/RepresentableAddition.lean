module
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # 表現可能な射の型の自然な演算と加法

概要：後合成に自然で零射を単位とする射の型の二項演算は、前加法圏の加法と一致する。
方針：二項双積の二射影で演算を計算し、和を取る射へ後合成する。
規約：演算の結合性や可換性は仮定しない。使われ方：ループ演算から得る逆元と射の負号の比較。
-/
@[expose] public section
universe v u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：後合成に自然で零射を左右の単位とする表現可能な射の型の演算は加法。
方針：二つの射を双積の別々の成分に入れ、射影で演算を判定した後に余対角へ合成する。
規約：前加法構造と二項双積だけを使う。使われ方：空間から移した演算の加法との照合。 -/
lemma representableOperation_eq_add {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (A : C)
    (μ : ∀ B : C, (A ⟶ B) → (A ⟶ B) → (A ⟶ B))
    (hleft : ∀ (B : C) (f : A ⟶ B), μ B 0 f = f)
    (hright : ∀ (B : C) (f : A ⟶ B), μ B f 0 = f)
    (hnat : ∀ (B D : C) (f g : A ⟶ B) (h : B ⟶ D),
      μ B f g ≫ h = μ D (f ≫ h) (g ≫ h))
    (B : C) (f g : A ⟶ B) : μ B f g = f + g := by
  have hpair : μ (B ⊞ B) (biprod.lift f 0) (biprod.lift 0 g) = biprod.lift f g := by
    apply biprod.hom_ext
    · rw [hnat]
      simp only [biprod.lift_fst, hright]
    · rw [hnat]
      simp only [biprod.lift_snd, hleft]
  have h := congrArg (fun k => k ≫ biprod.desc (𝟙 B) (𝟙 B)) hpair
  rw [hnat] at h
  simpa only [biprod.lift_desc, Category.comp_id, zero_add, add_zero] using h

/-- 概要：零単位と後合成の自然性を持つ演算の右逆元は既存の加法の負号。
方針：演算を加法に同定して左から同じ射を加えた等号を消去する。
規約：右逆元の選択の自然性は不要。使われ方：交換がループ逆元であることから負号へ移す。 -/
lemma representableRightInverse_eq_neg {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (A : C)
    (μ : ∀ B : C, (A ⟶ B) → (A ⟶ B) → (A ⟶ B))
    (hleft : ∀ (B : C) (f : A ⟶ B), μ B 0 f = f)
    (hright : ∀ (B : C) (f : A ⟶ B), μ B f 0 = f)
    (hnat : ∀ (B D : C) (f g : A ⟶ B) (h : B ⟶ D),
      μ B f g ≫ h = μ D (f ≫ h) (g ≫ h))
    (ν : ∀ B : C, (A ⟶ B) → (A ⟶ B))
    (hinv : ∀ (B : C) (f : A ⟶ B), μ B f (ν B f) = 0)
    (B : C) (f : A ⟶ B) : ν B f = -f := by
  apply add_left_cancel (a := f)
  rw [add_neg_cancel, ← representableOperation_eq_add A μ hleft hright hnat]
  exact hinv B f

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
