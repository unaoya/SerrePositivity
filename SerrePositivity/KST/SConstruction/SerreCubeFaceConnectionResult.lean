module
public import SerrePositivity.KST.SConstruction.CubeFaceNormalConnection
public import SerrePositivity.KST.SConstruction.SerreCubeFaceConnectionPrefix

/-! # 面の後の connection を移す計算結果の元の Serre 評価
概要：高々一つの元の入力操作と面の残余を、そのまま Serre 射として評価する。
方針：定数出力追加と入力保持への作用を、元の合成と tensor 合成で照合する。
規約：元の入力操作を厳密に回収する。使われ方：面・connection の標準化の評価保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 面の後の connection を移した結果の、元の Serre 射としての評価。 -/
def serreCubeFaceConnectionResult : {n m : ℕ} → CubeFaceConnectionResult n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, _, .pure d => serreCubeFaceNormal A d
  | _, _, .input i d => serreCubeDegeneracy A _ i ≫ serreCubeFaceNormal A d
  | _, _, .connect i d => serreCubeConnection A _ i ≫ serreCubeFaceNormal A d

/-- 結果への定数出力の追加は、元の同じ Serre 面の後合成。 -/
lemma serreCubeFaceConnectionResult_point {n m : ℕ} (b : Bool)
    (r : CubeFaceConnectionResult n m) :
    serreCubeFaceConnectionResult A (cubeFaceConnectionResultPoint b r) =
      serreCubeFaceConnectionResult A r ≫ serreCubeFace A b m 0 := by
  cases r with
  | pure d => rfl
  | input i d => exact (Category.assoc _ _ _).symm
  | connect i d => exact (Category.assoc _ _ _).symm

/-- 結果への入力保持は、元の同じ Serre 射と恒等の tensor。 -/
lemma serreCubeFaceConnectionResult_keep {n m : ℕ} (r : CubeFaceConnectionResult n m) :
    serreCubeFaceConnectionResult A (cubeFaceConnectionResultKeep r) =
      serreCubeFaceConnectionResult A r ⊗ₘ 𝟙 (serreIntervalComonoid A) := by
  cases r with
  | pure d => rfl
  | input i d =>
    change (serreCubeDegeneracy A _ i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
        (serreCubeDegeneracy A _ i ≫ serreCubeFaceNormal A d) ⊗ₘ
          𝟙 (serreIntervalComonoid A)
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  | connect i d =>
    change (serreCubeConnection A _ i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
        (serreCubeConnection A _ i ≫ serreCubeFaceNormal A d) ⊗ₘ
          𝟙 (serreIntervalComonoid A)
    simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
