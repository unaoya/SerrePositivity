module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SplitPairCoherence

/-!
模型。文献の定義との比較は後で
# 末尾二因子の交換の単位子と結合子の整合性

概要：Berger–Moerdijk §1 の末尾交換の帰納法に必要な構造射の等式を証明する。
方針：一般のモノイダル圏で単位子・結合子の自然性を用いる。
規約：交換する二因子の前の因子は固定する。
使われ方：末尾交換と分離の可換性の基底と帰納段階に用いる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 概要：分離後の対への射は先頭の因子との逆結合子を通して適用できる（Berger–Moerdijk §1）。
方針：whisker の合成則と結合子の右の自然性を使う。
規約：f は分離射、g は分離された対への任意の射。
使われ方：尾での交換と分離の可換性を先頭を付けた族へ持ち上げる。 -/
lemma splitPair_post_whiskerLeft (R : C) {X L Q Q' : C}
    (f : X ⟶ L ⊗ Q) (g : Q ⟶ Q') :
    (R ◁ (f ≫ (L ◁ g))) ≫ (α_ R L Q').inv =
      (R ◁ f) ≫ (α_ R L Q).inv ≫ ((R ⊗ L) ◁ g) := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right]

variable [BraidedCategory C]

/-- 概要：二因子と末尾の単位を交換してから分離する射は、分離後の二因子の交換に一致する（Berger–Moerdijk §1）。
方針：モノイダル整合性で右単位子をまとめ、左右の単位子の自然性で交換を移す。
規約：分離後の前半はテンソル単位。
使われ方：末尾交換と二因子の分離の可換性の帰納法の基底を与える。 -/
lemma swapPair_unit_separation (R S : C) :
    (α_ R S (𝟙_ C)).inv ≫ ((β_ R S).hom ▷ (𝟙_ C)) ≫
        (α_ S R (𝟙_ C)).hom ≫ (S ◁ (ρ_ R).hom) ≫ (λ_ (S ⊗ R)).inv =
      (R ◁ (ρ_ S).hom) ≫ (λ_ (R ⊗ S)).inv ≫ ((𝟙_ C) ◁ (β_ R S).hom) := by
  have hpost : (α_ S R (𝟙_ C)).hom ≫ (S ◁ (ρ_ R).hom) =
      (ρ_ (S ⊗ R)).hom := by monoidal
  have hpre : (α_ R S (𝟙_ C)).inv ≫ (ρ_ (R ⊗ S)).hom =
      R ◁ (ρ_ S).hom := by monoidal
  rw [← Category.assoc _ _ (λ_ (S ⊗ R)).inv, hpost,
    rightUnitor_naturality_assoc, ← Category.assoc, hpre,
    leftUnitor_inv_naturality]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
