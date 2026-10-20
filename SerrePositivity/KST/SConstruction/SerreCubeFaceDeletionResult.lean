module
public import SerrePositivity.KST.SConstruction.CubeFaceNormalDeletion
public import SerrePositivity.KST.SConstruction.SerreCubeFaceDegeneracyRelations

/-! # 面の後の削除を移す計算結果の元の Serre 評価
概要：結果を高々一つの元の入力削除と元の面の残余の合成として評価する。
方針：定数出力の追加と入力保持への作用を、元の合成則と tensor 合成で照合する。
規約：元の Serre 余モノイド射を保持する。使われ方：混合語の正規化の評価保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 面の後の削除を移した結果の、元の Serre 射としての評価。 -/
def serreCubeFaceDeletionResult : {n m : ℕ} → CubeFaceDeletionResult n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, _, .pure d => serreCubeFaceNormal A d
  | _, _, .input i d => serreCubeDegeneracy A _ i ≫ serreCubeFaceNormal A d

/-- 計算結果への定数の追加は、元の同じ Serre 面の後合成を回収する。 -/
lemma serreCubeFaceDeletionResult_point {n m : ℕ} (b : Bool)
    (r : CubeFaceDeletionResult n m) :
    serreCubeFaceDeletionResult A (cubeFaceDeletionResultPoint b r) =
      serreCubeFaceDeletionResult A r ≫ serreCubeFace A b m 0 := by
  cases r with
  | pure d => rfl
  | input i d => exact (Category.assoc _ _ _).symm

/-- 計算結果への入力保持は、元の同じ Serre 射と恒等の tensor を回収する。 -/
lemma serreCubeFaceDeletionResult_keep {n m : ℕ} (r : CubeFaceDeletionResult n m) :
    serreCubeFaceDeletionResult A (cubeFaceDeletionResultKeep r) =
      serreCubeFaceDeletionResult A r ⊗ₘ 𝟙 (serreIntervalComonoid A) := by
  cases r with
  | pure d => rfl
  | input i d =>
    change (serreCubeDegeneracy A _ i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
        (serreCubeDegeneracy A _ i ≫ serreCubeFaceNormal A d) ⊗ₘ
          𝟙 (serreIntervalComonoid A)
    simp only [tensorHom_comp_tensorHom, Category.comp_id]

/-- 面の後の一出力削除を移す計算は、元の Serre 評価そのものを厳密に保存する。 -/
lemma serreCubeFaceNormal_delete {n m : ℕ} (d : CubeFaceNormal n (m + 1))
    (i : Fin (m + 1)) :
    serreCubeFaceDeletionResult A (cubeFaceNormalDelete d i) =
      serreCubeFaceNormal A d ≫ serreCubeDegeneracy A m i := by
  induction m generalizing n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    cases d with
    | point b d =>
      change serreCubeFaceNormal A d =
        (serreCubeFaceNormal A d ≫ serreCubeFace A b 0 0) ≫ serreCubeDegeneracy A 0 0
      rw [Category.assoc, serreCubeFace_zero_degeneracy, Category.comp_id]
    | keep d =>
      exact (serreCubeDegeneracy_zero_naturality A (serreCubeFaceNormal A d)).symm
  | succ m ih =>
    cases d with
    | point b d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change serreCubeFaceNormal A d =
          (serreCubeFaceNormal A d ≫ serreCubeFace A b (m + 1) 0) ≫
            serreCubeDegeneracy A (m + 1) 0
        rw [Category.assoc, serreCubeFace_zero_degeneracy, Category.comp_id]
      · change serreCubeFaceDeletionResult A
          (cubeFaceDeletionResultPoint b (cubeFaceNormalDelete d i)) = _
        rw [serreCubeFaceDeletionResult_point, ih d i]
        change (serreCubeFaceNormal A d ≫ serreCubeDegeneracy A m i) ≫
          serreCubeFace A b m 0 =
            (serreCubeFaceNormal A d ≫ serreCubeFace A b (m + 1) 0) ≫
              serreCubeDegeneracy A (m + 1) i.succ
        simp only [Category.assoc]
        rw [serreCubeFace_degeneracy_right_zero]
    | keep d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · exact (serreCubeDegeneracy_zero_naturality A (serreCubeFaceNormal A d)).symm
      · change serreCubeFaceDeletionResult A
          (cubeFaceDeletionResultKeep (cubeFaceNormalDelete d i)) = _
        rw [serreCubeFaceDeletionResult_keep]
        change (serreCubeFaceDeletionResult A (cubeFaceNormalDelete d i) ⊗ₘ
            𝟙 (serreIntervalComonoid A)) =
          (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
            (serreCubeDegeneracy A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [ih d i]
        simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
