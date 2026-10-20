module
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateMaps

/-! # Serre 鎖立方体の座標射の対角・増大保存
概要：全座標の面・退化・connection の元の鎖写像は、同じ Serre 対角と増大を保つ。
方針：余モノイド射の法則を適用し、各座標射の再帰式を回収する。
規約：座標は右端から数える。使われ方：cubical 座標作用と tensor 比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 右端への挿入は、元の右単位同型と端点射の tensor。 -/
lemma serreCubeFace_zero (b : Bool) (n : ℕ) :
    serreCubeFace A b n 0 = (ρ_ (serreCubeComonoid A n)).inv ≫
      (𝟙 (serreCubeComonoid A n) ⊗ₘ serreIntervalEndpointComonHom A b) := by
  cases n <;> rfl

/-- 内側の座標の面は、一段小さい同じ面と恒等射の tensor。 -/
lemma serreCubeFace_succ (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A b (n + 1) i.succ =
      serreCubeFace A b n i ⊗ₘ 𝟙 (serreIntervalComonoid A) := rfl

/-- 右端の削除は、元の増大写像と右単位同型。 -/
lemma serreCubeDegeneracy_zero (n : ℕ) :
    serreCubeDegeneracy A n 0 =
      (𝟙 (serreCubeComonoid A n) ⊗ₘ serreIntervalAugmentationComonHom A) ≫
        (ρ_ (serreCubeComonoid A n)).hom := by
  cases n <;> rfl

/-- 内側の座標の削除は、一段小さい同じ削除と恒等射の tensor。 -/
lemma serreCubeDegeneracy_succ (n : ℕ) (i : Fin (n + 1)) :
    serreCubeDegeneracy A (n + 1) i.succ =
      serreCubeDegeneracy A n i ⊗ₘ 𝟙 (serreIntervalComonoid A) := rfl

/-- 右端二座標の connection は、元の結合同型と max 射。 -/
lemma serreCubeConnection_zero (n : ℕ) :
    serreCubeConnection A n 0 =
      (α_ (serreCubeComonoid A n) (serreIntervalComonoid A) (serreIntervalComonoid A)).hom ≫
        (𝟙 (serreCubeComonoid A n) ⊗ₘ serreIntervalMaxComonHom A) := by
  cases n <;> rfl

/-- 内側の connection は、一段小さい同じ connection と恒等射の tensor。 -/
lemma serreCubeConnection_succ (n : ℕ) (i : Fin (n + 1)) :
    serreCubeConnection A (n + 1) i.succ =
      serreCubeConnection A n i ⊗ₘ 𝟙 (serreIntervalComonoid A) := rfl

/-- 全座標の面の元の鎖写像は、Serre 対角を保持する。 -/
lemma serreCubeFace_diagonal (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeFace A b n i).hom ≫ serreCubeDiagonal A (n + 1) =
      serreCubeDiagonal A n ≫ ((serreCubeFace A b n i).hom ⊗ₘ (serreCubeFace A b n i).hom) :=
  IsComonHom.hom_comul (serreCubeFace A b n i).hom

/-- 全座標の退化の元の鎖写像は、Serre 対角を保持する。 -/
lemma serreCubeDegeneracy_diagonal (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeDegeneracy A n i).hom ≫ serreCubeDiagonal A n =
      serreCubeDiagonal A (n + 1) ≫
        ((serreCubeDegeneracy A n i).hom ⊗ₘ (serreCubeDegeneracy A n i).hom) :=
  IsComonHom.hom_comul (serreCubeDegeneracy A n i).hom

/-- 全座標の connection の元の鎖写像は、Serre 対角を保持する。 -/
lemma serreCubeConnection_diagonal (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeConnection A n i).hom ≫ serreCubeDiagonal A (n + 1) =
      serreCubeDiagonal A (n + 2) ≫
        ((serreCubeConnection A n i).hom ⊗ₘ (serreCubeConnection A n i).hom) :=
  IsComonHom.hom_comul (serreCubeConnection A n i).hom

/-- 全座標の面の元の鎖写像は、増大写像を保持する。 -/
lemma serreCubeFace_augmentation (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeFace A b n i).hom ≫ serreCubeAugmentation A (n + 1) =
      serreCubeAugmentation A n :=
  IsComonHom.hom_counit (serreCubeFace A b n i).hom

/-- 全座標の退化の元の鎖写像は、増大写像を保持する。 -/
lemma serreCubeDegeneracy_augmentation (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeDegeneracy A n i).hom ≫ serreCubeAugmentation A n =
      serreCubeAugmentation A (n + 1) :=
  IsComonHom.hom_counit (serreCubeDegeneracy A n i).hom

/-- 全座標の connection の元の鎖写像は、増大写像を保持する。 -/
lemma serreCubeConnection_augmentation (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeConnection A n i).hom ≫ serreCubeAugmentation A (n + 1) =
      serreCubeAugmentation A (n + 2) :=
  IsComonHom.hom_counit (serreCubeConnection A n i).hom

end SerrePositivity.KST.SConstruction
