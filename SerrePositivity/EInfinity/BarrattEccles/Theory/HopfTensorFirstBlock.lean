module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorOperations
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorFirstBlockCoherence

/-!
# テンソル冪の先頭ブロックへの演算

## 概要
Berger–Fresse §1.1.4 のテンソル演算と先頭ブロックへの代入を二列に分離する。

## 方針
連結と二列分離の比較を逆向きの連結へ移し、一般の先頭ブロックの図式を使う。

## 規約
係数射は任意でよく、零個の入力と零個の残り入力を含める。

## 使われ方
HA 3.2.4.7 のテンソル比較で使う代数の先頭部分合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- BF §1.1.4 の二列分離と、指定した連結の逆射との比較。 -/
@[reassoc]
lemma tensorPowerSeparation_append_inv (V W : Complex A) (n m : ℕ) :
    (appendIso (V ⊗ W) n m).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W m).hom) ≫
        tensorμ _ _ _ _ =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + m)).hom ≫
        ((appendIso V n m).inv ⊗ₘ (appendIso W n m).inv) := by
  apply (cancel_epi (appendIso (V ⊗ W) n m).hom).mp
  simp only [← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_append]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id,
    tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp]

/-- 指定された n 入力演算を最初の n 入力へ適用し、m 入力を残す（BF §1.1.4）。 -/
def tensorFirstAction (V C : Complex A) (n m : ℕ) (a : C ⊗ power V n ⟶ V) :
    C ⊗ power V (n + m) ⟶ power V (m + 1) :=
  (C ◁ (appendIso V n m).inv) ≫ (α_ C (power V n) (power V m)).inv ≫
    (a ▷ power V m)

/-- BF §1.1.4 のテンソル演算の先頭ブロックへの適用は二列へ分離する。 -/
lemma tensorFirstAction_separation (V W C C₁ C₂ : Complex A) (n m : ℕ)
    (d : C ⟶ C₁ ⊗ C₂) (a : C₁ ⊗ power V n ⟶ V) (b : C₂ ⊗ power W n ⟶ W) :
    tensorFirstAction (V ⊗ W) C n m
      ((d ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom) ≫ tensorμ _ _ _ _ ≫ (a ⊗ₘ b)) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (m + 1)).hom =
      (d ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + m)).hom) ≫ tensorμ _ _ _ _ ≫
        (tensorFirstAction V C₁ n m a ⊗ₘ tensorFirstAction W C₂ n m b) := by
  rw [tensorPowerSeparation_succ_hom]
  unfold tensorFirstAction
  simp only [Category.assoc]
  rw [← tensorHom_def_assoc, tensorFirstBlockAssembly,
    whiskerLeft_comp_tensorHom_assoc, tensorPowerSeparation_append_inv,
    ← tensorHom_comp_whiskerLeft_assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom]

end SerrePositivity.EInfinity
