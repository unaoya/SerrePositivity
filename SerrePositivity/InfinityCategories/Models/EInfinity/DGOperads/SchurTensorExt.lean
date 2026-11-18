module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Schur
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：左に固定因子を付けた Schur 対象からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：左テンソル関手で Schur 図式の余極限を保存する。
規約：固定因子も任意の非有界複体でよい。
使われ方：自由代数の演算の等式を各 arity の生成射へ帰着する。 -/
lemma schur_tensorLeft_hom_ext (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A)
    (f g : C ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ⟶ Y)
    (h : ∀ n : ℕ, (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n) ≫ f = (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorLeft C) (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K))).hom_ext
  intro S
  have hs := h S.card
  change (C ◁ colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card)) ≫ f =
    (C ◁ colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card)) ≫ g at hs
  rw [_root_.SerrePositivity.FiniteBijection.of_card] at hs
  exact hs

/-- 概要：右に固定因子を付けた Schur 対象からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：右テンソル関手の余極限保存に Schur 図式を適用する。
規約：固定因子を cofibrant と仮定しない。
使われ方：複数の Schur 入力を一つずつ生成射へ帰着する。 -/
lemma schur_tensorRight_hom_ext (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A)
    (f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ⊗ C ⟶ Y)
    (h : ∀ n : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ▷ C) ≫ f = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ▷ C) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorRight C) (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K))).hom_ext
  intro S
  have hs := h S.card
  change (colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card) ▷ C) ≫ f =
    (colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card) ▷ C) ≫ g at hs
  rw [_root_.SerrePositivity.FiniteBijection.of_card] at hs
  exact hs

/-- 概要：二つの Schur 対象のテンソルからの射は生成射のテンソル上で決まる（Berger–Moerdijk §1）。
方針：左右のテンソル関手の余極限保存を順に使う。
規約：両係数対称列と両入力複体は独立に選べる。
使われ方：自由代数の二入力の演算と合成則を生成射上で比較する。 -/
lemma schur_tensorPair_hom_ext (P Q : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K L Y : Complex A)
    (f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A Q).obj L ⟶ Y)
    (h : ∀ n m : ℕ, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A Q L m) ≫ f =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A Q L m) ≫ g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schur_tensorRight_hom_ext P K ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A Q).obj L) Y f g
  intro n
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schur_tensorLeft_hom_ext Q L (_root_.SerrePositivity.SymmetricSequence.level P n ⊗ power K n) Y
  intro m
  rw [← Category.assoc, ← Category.assoc, ← tensorHom_def']
  exact h n m

/-- 概要：二つの固定因子の間の Schur 因子からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：左右のテンソル関手の合成が Schur 図式の余極限を保存することを使う。
規約：固定因子は任意の非有界複体。
使われ方：任意個の Schur 入力の生成射による一意性を帰納的に示す。 -/
lemma schur_tensorMiddle_hom_ext (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C T Y : Complex A)
    (f g : C ⊗ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ⊗ T) ⟶ Y)
    (h : ∀ n : ℕ, (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ▷ T)) ≫ f =
      (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ▷ T)) ≫ g) : f = g := by
  change (C ⊗ (colimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) ⊗ T) ⟶ Y) at f g
  apply (cancel_epi (α_ C (colimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)) T).hom).1
  apply (isColimitOfPreserves (tensorLeft C ⋙ tensorRight T)
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K))).hom_ext
  intro S
  change ((C ◁ colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) S) ▷ T) ≫
    (α_ C (colimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)) T).hom ≫ f =
      ((C ◁ colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) S) ▷ T) ≫
        (α_ C (colimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)) T).hom ≫ g
  rw [associator_naturality_middle_assoc, associator_naturality_middle_assoc]
  have hs := h S.card
  change (C ◁ (colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card) ▷ T)) ≫ f =
    (C ◁ (colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (_root_.SerrePositivity.FiniteBijection.of S.card) ▷ T)) ≫ g at hs
  rw [_root_.SerrePositivity.FiniteBijection.of_card] at hs
  rw [hs]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
