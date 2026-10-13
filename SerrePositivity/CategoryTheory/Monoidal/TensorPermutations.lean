module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# 反復テンソルの隣接交換の基盤

最初の二因子を交換し、残りの因子をそのまま保つ同型を構成する。
対合性と対象の射に関する自然性を確認する。
全ての置換の作用を定義するには、他の位置の交換とその関係式をさらに整える必要がある。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 最初の二因子を交換する反復テンソルの同型。 -/
def swapFirstIso (X : C) (n : ℕ) : power X (n + 2) ≅ power X (n + 2) :=
  (α_ X X (power X n)).symm ≪≫ whiskerRightIso (β_ X X) (power X n) ≪≫ α_ X X (power X n)

/-- 最初の二因子の交換は対合。 -/
lemma swapFirstIso_involutive (X : C) (n : ℕ) :
    (swapFirstIso X n).hom ≫ (swapFirstIso X n).hom = 𝟙 (power X (n + 2)) := by
  simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp

/-- 最初の二因子の交換は基礎圏の射と両立する。 -/
lemma swapFirstIso_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    map f (n + 2) ≫ (swapFirstIso Y n).hom =
      (swapFirstIso X n).hom ≫ map f (n + 2) := by
  simp only [swapFirstIso, map, power, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [associator_inv_naturality_assoc]
  have h : ((f ⊗ₘ f) ⊗ₘ map f n) ≫ ((β_ Y Y).hom ▷ power Y n) =
      ((β_ X X).hom ▷ power X n) ≫ ((f ⊗ₘ f) ⊗ₘ map f n) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun k ↦ k ⊗ₘ map f n) (braiding_naturality f f)
  rw [← Category.assoc _ _ (α_ Y Y (power Y n)).hom, h, Category.assoc,
    associator_naturality]

end SerrePositivity.TensorPowers
