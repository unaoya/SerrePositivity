module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HadamardCoherence

/-!
# 二列の作用の合成の組み立て

## 概要
BF §1.1.4 の Hopf 対角による作用で、二段の合成を各列の合成則へ帰着する。

## 方針
Hadamard 積の左右の反復合成と結合子の自然性を使い、指定された全ての射を保持する。

## 規約
対角の合成則と入力の比較は射の等式として受け取り、モデル構造は要求しない。

## 使われ方
HA 3.2.4.7 の比較先のテンソル代数の部分合成則。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

/-- BF §1.1.4 の係数と入力の分離から二列の作用を組み立てる。 -/
def tensorActionAssembly {O N O₁ O₂ N₁ N₂ V W : K}
    (d : O ⟶ O₁ ⊗ O₂) (s : N ⟶ N₁ ⊗ N₂)
    (a : O₁ ⊗ N₁ ⟶ V) (b : O₂ ⊗ N₂ ⟶ W) : O ⊗ N ⟶ V ⊗ W :=
  (d ⊗ₘ s) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair a b

/-- BF §1.1.4 の指定対角と入力の比較に沿って、二列の合成則を移す。 -/
lemma tensorActionAssembly_composition
    {O B C N M O₁ O₂ B₁ B₂ C₁ C₂ N₁ N₂ M₁ M₂ V W : K}
    (dO : O ⟶ O₁ ⊗ O₂) (dB : B ⟶ B₁ ⊗ B₂) (dC : C ⟶ C₁ ⊗ C₂)
    (s : N ⟶ N₁ ⊗ N₂) (t : M ⟶ M₁ ⊗ M₂)
    (c : O ⊗ B ⟶ C) (c₁ : O₁ ⊗ B₁ ⟶ C₁) (c₂ : O₂ ⊗ B₂ ⟶ C₂)
    (a : C₁ ⊗ N₁ ⟶ V) (b : C₂ ⊗ N₂ ⟶ W)
    (a' : O₁ ⊗ M₁ ⟶ V) (b' : O₂ ⊗ M₂ ⟶ W)
    (i : B ⊗ N ⟶ M) (i₁ : B₁ ⊗ N₁ ⟶ M₁) (i₂ : B₂ ⊗ N₂ ⟶ M₂)
    (hc : c ≫ dC = (dO ⊗ₘ dB) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair c₁ c₂)
    (ha : (c₁ ▷ N₁) ≫ a = (α_ O₁ B₁ N₁).hom ≫ (O₁ ◁ i₁) ≫ a')
    (hb : (c₂ ▷ N₂) ≫ b = (α_ O₂ B₂ N₂).hom ≫ (O₂ ◁ i₂) ≫ b')
    (hi : i ≫ t = tensorActionAssembly dB s i₁ i₂) :
    (c ▷ N) ≫ tensorActionAssembly dC s a b =
      (α_ O B N).hom ≫ (O ◁ i) ≫ tensorActionAssembly dO t a' b' := by
  unfold tensorActionAssembly at hi ⊢
  rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hc, Category.id_comp,
    ← tensorHom_comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_left, ha, hb,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_right, associator_naturality_assoc,
    tensorHom_comp_whiskerLeft_assoc, ← hi, ← whiskerLeft_comp_tensorHom_assoc]

end SerrePositivity.EInfinity
