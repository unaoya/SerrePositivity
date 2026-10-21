module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomValues
public import SerrePositivity.KST.SConstruction.MonoidalRightBlockNaturality

/-! # 元の鎖の右ブロックの零座標と連結比較
概要：元の端点挿入・増大・max と、左ブロックを分離する鎖比較の可換性を証明する。
方針：鎖立方体の元の座標再帰式を、抽象モノイダル圏の三操作の式へ接続する。
規約：全次元と tensor の四対象を明示する。使われ方：全座標の右因子自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右ブロックの零面は、同じ連結比較と可換。 -/
lemma serreCubeTensor_rightFace_zero (n m : ℕ) (b : Bool) :
    serreCubeFace A b (n + m) 0 ≫ (serreCubeTensorIso A n (m + 1)).hom =
      (serreCubeTensorIso A n m).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := m) (q := m + 1)
          (𝟙 (serreCubeComonoid A n)) (serreCubeFace A b m 0) := by
  have ht := monoidalRightBlock_insert (R := serreCubeComonoid A (n + m))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m) (I := serreIntervalComonoid A)
    (serreCubeTensorIso A n m).hom (serreIntervalEndpointComonHom A b)
  erw [serreCubeFace_zero A b (n + m), serreCubeFace_zero A b m]
  dsimp only [serreCubeTensorHom, serreCubeTensorIso_succ,
    Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  erw [Category.assoc]
  exact ht

/-- 元の右ブロックの零削除は、同じ連結比較と可換。 -/
lemma serreCubeTensor_rightDegeneracy_zero (n m : ℕ) :
    serreCubeDegeneracy A (n + m) 0 ≫ (serreCubeTensorIso A n m).hom =
      (serreCubeTensorIso A n (m + 1)).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := m + 1) (q := m)
          (𝟙 (serreCubeComonoid A n)) (serreCubeDegeneracy A m 0) := by
  have ht := monoidalRightBlock_delete (R := serreCubeComonoid A (n + m))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m) (I := serreIntervalComonoid A)
    (serreCubeTensorIso A n m).hom (serreIntervalAugmentationComonHom A)
  erw [serreCubeDegeneracy_zero A (n + m), serreCubeDegeneracy_zero A m]
  dsimp only [serreCubeTensorHom, serreCubeTensorIso_succ,
    Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  erw [Category.assoc, Category.assoc]
  exact ht

/-- 元の右ブロックの零 max は、同じ二段の連結比較と可換。 -/
lemma serreCubeTensor_rightConnection_zero (n m : ℕ) :
    serreCubeConnection A (n + m) 0 ≫ (serreCubeTensorIso A n (m + 1)).hom =
      (serreCubeTensorIso A n (m + 2)).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := m + 2) (q := m + 1)
          (𝟙 (serreCubeComonoid A n)) (serreCubeConnection A m 0) := by
  have ht := monoidalRightBlock_multiply_iso (C := Comon (Complex A))
    (R := serreCubeComonoid A (n + m))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m) (I := serreIntervalComonoid A)
    (serreCubeTensorIso A n m) (serreIntervalMaxComonHom A)
  erw [serreCubeConnection_zero A (n + m), serreCubeConnection_zero A m]
  erw [serreCubeTensorIso_succ A n (m + 1), serreCubeTensorIso_succ A n m]
  dsimp only [serreCubeTensorHom]
  dsimp only [serreCubeComonoid] at ht ⊢
  apply Comon.ext
  exact congrArg (fun f => f.hom) ht

end SerrePositivity.KST.SConstruction
