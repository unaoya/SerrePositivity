module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Mon

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
open _root_.CategoryTheory Limits MonoidalCategory MonoidalPreadditive Preadditive
open scoped _root_.CategoryTheory.MonObj
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
end SerrePositivity.KST.LocalizingInvariants.SquareZero
namespace SerrePositivity.InfinityCategories.HA.Section7_3_4
open _root_.SerrePositivity.KST.LocalizingInvariants.SquareZero

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (A : Mon C) (M : Bimod A A) [HasBinaryBiproduct A.X M.X]

abbrev obj : C := A.X ⊞ M.X

def one : 𝟙_ C ⟶ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M := η[A.X] ≫ biprod.inl

def mul : _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ⊗ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ⟶ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M :=
  (biprod.fst ⊗ₘ biprod.fst) ≫ μ[A.X] ≫ biprod.inl +
    ((biprod.fst ⊗ₘ biprod.snd) ≫ M.actLeft +
      (biprod.snd ⊗ₘ biprod.fst) ≫ M.actRight) ≫ biprod.inr

@[reassoc (attr := simp)]
lemma mul_ll : (biprod.inl ⊗ₘ biprod.inl) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = μ[A.X] ≫ biprod.inl := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_lr : (biprod.inl ⊗ₘ biprod.inr) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = M.actLeft ≫ biprod.inr := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_rl : (biprod.inr ⊗ₘ biprod.inl) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = M.actRight ≫ biprod.inr := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul, tensorHom_comp_tensorHom_assoc]

@[reassoc (attr := simp)]
lemma mul_rr : (biprod.inr ⊗ₘ biprod.inr) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul, tensorHom_comp_tensorHom_assoc]

lemma mul_fst : _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ biprod.fst = (biprod.fst ⊗ₘ biprod.fst) ≫ μ[A.X] := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul]

lemma mul_snd : _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ biprod.snd =
    (biprod.fst ⊗ₘ biprod.snd) ≫ M.actLeft +
      (biprod.snd ⊗ₘ biprod.fst) ≫ M.actRight := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul]

end SerrePositivity.InfinityCategories.HA.Section7_3_4

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section















/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.3.4.16" (partial := component) "仮定：前加法モノイダル通常圏、内部代数 A と A 双加群 M、二項直和（Lean が強い：厳密な dg 複体を含む通常圏模型の場合）。結論：A⊕M の単位と積の四成分を計算し、M⊗M 成分の積が零となる（HA の平方零積の公式の部分に一致）。Ω∞ によって得た HA の代数構造との比較と一般の安定 ∞ 圏は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll
attribute [cite HA "7.3.4.16" (partial := component) "仮定：前加法モノイダル通常圏、内部代数 A と A 双加群 M、二項直和（Lean が強い：厳密な dg 複体を含む通常圏模型の場合）。結論：A⊕M の単位と積の四成分を計算し、M⊗M 成分の積が零となる（HA の平方零積の公式の部分に一致）。Ω∞ によって得た HA の代数構造との比較と一般の安定 ∞ 圏は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr
attribute [cite HA "7.3.4.16" (partial := component) "仮定：前加法モノイダル通常圏、内部代数 A と A 双加群 M、二項直和（Lean が強い：厳密な dg 複体を含む通常圏模型の場合）。結論：A⊕M の単位と積の四成分を計算し、M⊗M 成分の積が零となる（HA の平方零積の公式の部分に一致）。Ω∞ によって得た HA の代数構造との比較と一般の安定 ∞ 圏は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl
attribute [cite HA "7.3.4.16" (partial := component) "仮定：前加法モノイダル通常圏、内部代数 A と A 双加群 M、二項直和（Lean が強い：厳密な dg 複体を含む通常圏模型の場合）。結論：A⊕M の単位と積の四成分を計算し、M⊗M 成分の積が零となる（HA の平方零積の公式の部分に一致）。Ω∞ によって得た HA の代数構造との比較と一般の安定 ∞ 圏は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr
attribute [cite HA "7.3.4.16" (partial := component) "仮定：前加法モノイダル通常圏、内部代数 A と A 双加群 M、二項直和（Lean が強い：厳密な dg 複体を含む通常圏模型の場合）。結論：A⊕M の単位と積の四成分を計算し、M⊗M 成分の積が零となる（HA の平方零積の公式の部分に一致）。Ω∞ によって得た HA の代数構造との比較と一般の安定 ∞ 圏は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one
