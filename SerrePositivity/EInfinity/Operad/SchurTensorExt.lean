module

public import SerrePositivity.EInfinity.Operad.Schur
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-!
# Schur 生成射をテンソルした射の一意性

概要：Berger–Moerdijk §1 の自由代数の演算をテンソルの生成射上で比較する。
方針：閉モノイダル構造からテンソル関手の余極限保存を使う。
規約：Schur 対象に代数構造があるとは仮定しない。
使われ方：自由代数の作用の降下と代数の公理を生成射上で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：左に固定因子を付けた Schur 対象からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：左テンソル関手で Schur 図式の余極限を保存する。
規約：固定因子も任意の非有界複体でよい。
使われ方：自由代数の演算の等式を各 arity の生成射へ帰着する。 -/
lemma schur_tensorLeft_hom_ext (P : SymmetricSequence (Complex A)) (K C Y : Complex A)
    (f g : C ⊗ (schurFunctor A P).obj K ⟶ Y)
    (h : ∀ n : ℕ, (C ◁ schurι A P K n) ≫ f = (C ◁ schurι A P K n) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorLeft C) (colimit.isColimit (schurDiagram A P K))).hom_ext
  intro S
  have hs := h S.card
  change (C ◁ colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card)) ≫ f =
    (C ◁ colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card)) ≫ g at hs
  rw [FiniteBijection.of_card] at hs
  exact hs

/-- 概要：右に固定因子を付けた Schur 対象からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：右テンソル関手の余極限保存に Schur 図式を適用する。
規約：固定因子を cofibrant と仮定しない。
使われ方：複数の Schur 入力を一つずつ生成射へ帰着する。 -/
lemma schur_tensorRight_hom_ext (P : SymmetricSequence (Complex A)) (K C Y : Complex A)
    (f g : (schurFunctor A P).obj K ⊗ C ⟶ Y)
    (h : ∀ n : ℕ, (schurι A P K n ▷ C) ≫ f = (schurι A P K n ▷ C) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorRight C) (colimit.isColimit (schurDiagram A P K))).hom_ext
  intro S
  have hs := h S.card
  change (colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ▷ C) ≫ f =
    (colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ▷ C) ≫ g at hs
  rw [FiniteBijection.of_card] at hs
  exact hs

/-- 概要：二つの Schur 対象のテンソルからの射は生成射のテンソル上で決まる（Berger–Moerdijk §1）。
方針：左右のテンソル関手の余極限保存を順に使う。
規約：両係数対称列と両入力複体は独立に選べる。
使われ方：自由代数の二入力の演算と合成則を生成射上で比較する。 -/
lemma schur_tensorPair_hom_ext (P Q : SymmetricSequence (Complex A)) (K L Y : Complex A)
    (f g : (schurFunctor A P).obj K ⊗ (schurFunctor A Q).obj L ⟶ Y)
    (h : ∀ n m : ℕ, (schurι A P K n ⊗ₘ schurι A Q L m) ≫ f =
      (schurι A P K n ⊗ₘ schurι A Q L m) ≫ g) : f = g := by
  apply schur_tensorRight_hom_ext P K ((schurFunctor A Q).obj L) Y f g
  intro n
  apply schur_tensorLeft_hom_ext Q L (SymmetricSequence.level P n ⊗ power K n) Y
  intro m
  rw [← Category.assoc, ← Category.assoc, ← tensorHom_def']
  exact h n m

/-- 概要：二つの固定因子の間の Schur 因子からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：左右のテンソル関手の合成が Schur 図式の余極限を保存することを使う。
規約：固定因子は任意の非有界複体。
使われ方：任意個の Schur 入力の生成射による一意性を帰納的に示す。 -/
lemma schur_tensorMiddle_hom_ext (P : SymmetricSequence (Complex A)) (K C T Y : Complex A)
    (f g : C ⊗ ((schurFunctor A P).obj K ⊗ T) ⟶ Y)
    (h : ∀ n : ℕ, (C ◁ (schurι A P K n ▷ T)) ≫ f =
      (C ◁ (schurι A P K n ▷ T)) ≫ g) : f = g := by
  change (C ⊗ (colimit (schurDiagram A P K) ⊗ T) ⟶ Y) at f g
  apply (cancel_epi (α_ C (colimit (schurDiagram A P K)) T).hom).1
  apply (isColimitOfPreserves (tensorLeft C ⋙ tensorRight T)
    (colimit.isColimit (schurDiagram A P K))).hom_ext
  intro S
  change ((C ◁ colimit.ι (schurDiagram A P K) S) ▷ T) ≫
    (α_ C (colimit (schurDiagram A P K)) T).hom ≫ f =
      ((C ◁ colimit.ι (schurDiagram A P K) S) ▷ T) ≫
        (α_ C (colimit (schurDiagram A P K)) T).hom ≫ g
  rw [associator_naturality_middle_assoc, associator_naturality_middle_assoc]
  have hs := h S.card
  change (C ◁ (colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ▷ T)) ≫ f =
    (C ◁ (colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ▷ T)) ≫ g at hs
  rw [FiniteBijection.of_card] at hs
  rw [hs]

end SerrePositivity.EInfinity
