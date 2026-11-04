module

public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
概要：実双加群から、直和上の分裂平方零拡大の単位と積を構成する。
方針：代数の積と左右作用を直和射影で組み合わせ、四つの成分を厳密に計算する。
規約：非可換双加群を使用。使われ方：derivation を切断として表示する実 dg 代数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive Preadditive
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (A : Mon C) (M : Bimod A A) [HasBinaryBiproduct A.X M.X]

abbrev obj : C := A.X ⊞ M.X

def one : 𝟙_ C ⟶ obj A M := η[A.X] ≫ biprod.inl

def mul : obj A M ⊗ obj A M ⟶ obj A M :=
  (biprod.fst ⊗ₘ biprod.fst) ≫ μ[A.X] ≫ biprod.inl +
    ((biprod.fst ⊗ₘ biprod.snd) ≫ M.actLeft +
      (biprod.snd ⊗ₘ biprod.fst) ≫ M.actRight) ≫ biprod.inr

@[reassoc (attr := simp)]
lemma mul_ll : (biprod.inl ⊗ₘ biprod.inl) ≫ mul A M = μ[A.X] ≫ biprod.inl := by
  simp [mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_lr : (biprod.inl ⊗ₘ biprod.inr) ≫ mul A M = M.actLeft ≫ biprod.inr := by
  simp [mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_rl : (biprod.inr ⊗ₘ biprod.inl) ≫ mul A M = M.actRight ≫ biprod.inr := by
  simp [mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_rr : (biprod.inr ⊗ₘ biprod.inr) ≫ mul A M = 0 := by
  simp [mul, tensorHom_comp_tensorHom_assoc]

lemma mul_fst : mul A M ≫ biprod.fst = (biprod.fst ⊗ₘ biprod.fst) ≫ μ[A.X] := by
  simp [mul]

lemma mul_snd : mul A M ≫ biprod.snd =
    (biprod.fst ⊗ₘ biprod.snd) ≫ M.actLeft +
      (biprod.snd ⊗ₘ biprod.fst) ≫ M.actRight := by
  simp [mul]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
