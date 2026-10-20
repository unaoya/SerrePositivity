module
public import SerrePositivity.KST.SConstruction.SerreIntervalCoassociativity
public import SerrePositivity.KST.SConstruction.SerreIntervalCounit
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 有限鎖立方体の Serre 余モノイド
概要：元の鎖区間の Serre 対角を余モノイドへ束ね、全有限 tensor 冪へ移す。
方針：区間で証明した余結合・余単位律と、既存の braided tensor 余モノイドを使う。
規約：交差は元の signed braiding。使われ方：cubical rigidification の tensor 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の区間の Serre 対角・増大写像による余モノイド構造。 -/
instance serreIntervalComonObj : ComonObj (serreInterval A) where
  counit := serreIntervalAugmentation A
  comul := serreIntervalDiagonal A
  counit_comul := by
    apply (cancel_mono (λ_ (serreInterval A)).hom).1
    rw [Category.assoc, Iso.inv_hom_id]
    simpa only [tensorHom_id] using serreIntervalDiagonal_left_counit A
  comul_counit := by
    apply (cancel_mono (ρ_ (serreInterval A)).hom).1
    rw [Category.assoc, Iso.inv_hom_id]
    simpa only [id_tensorHom] using serreIntervalDiagonal_right_counit A
  comul_assoc := (serreIntervalDiagonal_coassoc A).symm

/-- 元の鎖区間を保持する Serre 余モノイド。 -/
def serreIntervalComonoid : Comon (Complex A) := Comon.mk (serreInterval A)

/-- 元の鎖区間の全有限 tensor 冪の Serre 余モノイド。 -/
def serreCubeComonoid : ℕ → Comon (Complex A)
  | 0 => 𝟙_ (Comon (Complex A))
  | n + 1 => serreCubeComonoid n ⊗ serreIntervalComonoid A

/-- Serre 余モノイドの元の鎖立方体。 -/
abbrev serreCubeComplex (n : ℕ) : Complex A := (serreCubeComonoid A n).X

/-- 全有限鎖立方体の Serre 対角。 -/
def serreCubeDiagonal (n : ℕ) : serreCubeComplex A n ⟶
    serreCubeComplex A n ⊗ serreCubeComplex A n := ComonObj.comul

/-- 全有限鎖立方体の元の増大写像。 -/
def serreCubeAugmentation (n : ℕ) : serreCubeComplex A n ⟶ 𝟙_ (Complex A) :=
  ComonObj.counit

/-- 全有限鎖立方体の Serre 対角は、元の tensor 結合に沿って余結合的。 -/
lemma serreCubeDiagonal_coassoc (n : ℕ) :
    serreCubeDiagonal A n ≫ (serreCubeDiagonal A n ⊗ₘ 𝟙 _) ≫
        (α_ (serreCubeComplex A n) (serreCubeComplex A n) (serreCubeComplex A n)).hom =
      serreCubeDiagonal A n ≫ (𝟙 _ ⊗ₘ serreCubeDiagonal A n) :=
  (ComonObj.comul_assoc (serreCubeComplex A n)).symm

/-- 全有限鎖立方体の対角の左余単位律。 -/
lemma serreCubeDiagonal_left_counit (n : ℕ) :
    serreCubeDiagonal A n ≫ (serreCubeAugmentation A n ⊗ₘ 𝟙 _) ≫
        (λ_ (serreCubeComplex A n)).hom = 𝟙 _ := by
  change ComonObj.comul ≫ ComonObj.counit ▷ serreCubeComplex A n ≫
    (λ_ (serreCubeComplex A n)).hom = 𝟙 _
  rw [← Category.assoc, ComonObj.counit_comul, Iso.inv_hom_id]

/-- 全有限鎖立方体の対角の右余単位律。 -/
lemma serreCubeDiagonal_right_counit (n : ℕ) :
    serreCubeDiagonal A n ≫ (𝟙 _ ⊗ₘ serreCubeAugmentation A n) ≫
        (ρ_ (serreCubeComplex A n)).hom = 𝟙 _ := by
  change ComonObj.comul ≫ serreCubeComplex A n ◁ ComonObj.counit ≫
    (ρ_ (serreCubeComplex A n)).hom = 𝟙 _
  rw [← Category.assoc, ComonObj.comul_counit, Iso.inv_hom_id]

/-- 座標を一つ増やした Serre 対角は、元の tensor の signed 交差を持つ。 -/
lemma serreCubeDiagonal_succ (n : ℕ) :
    serreCubeDiagonal A (n + 1) =
      (serreCubeDiagonal A n ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreCubeComplex A n) (serreCubeComplex A n)
          (serreInterval A) (serreInterval A) :=
  Comon.tensorObj_comul (serreCubeComplex A n) (serreInterval A)

end SerrePositivity.KST.SConstruction
