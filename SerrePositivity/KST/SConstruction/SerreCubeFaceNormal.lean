module
public import SerrePositivity.KST.SConstruction.CubeFaceNormalDetection
public import SerrePositivity.KST.SConstruction.SerreCubeFaceRelations

/-! # 定数・保持標準表示の元の Serre 評価
概要：元の端点挿入と tensor 恒等で標準表示を評価し、任意座標の面との整合性を示す。
方針：面同士の交換関係と tensor 合成則で標準表示を帰納する。
規約：元の Serre 余モノイド射そのものを比較する。使われ方：面のみの語の表示非依存性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 定数・保持標準表示の元の Serre 余モノイド射による評価。 -/
def serreCubeFaceNormal : {n m : ℕ} → CubeFaceNormal n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, _, .nil => 𝟙 _
  | _, _, .point b d => serreCubeFaceNormal d ≫ serreCubeFace A b _ 0
  | _, _, .keep d => serreCubeFaceNormal d ⊗ₘ 𝟙 (serreIntervalComonoid A)

/-- 全入力を保持する面の標準表示は、元の Serre 恒等射。 -/
lemma serreCubeFaceNormal_id (n : ℕ) :
    serreCubeFaceNormal A (cubeFaceNormalId n) = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (serreCubeFaceNormal A (cubeFaceNormalId n) ⊗ₘ
      𝟙 (serreIntervalComonoid A)) = 𝟙 _
    rw [ih]
    simp

/-- 標準表示への一面挿入は、元の同じ Serre 面との合成を厳密に回収する。 -/
lemma serreCubeFaceNormal_insert {n m : ℕ} (d : CubeFaceNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    serreCubeFaceNormal A (cubeFaceNormalInsert d b i) =
      serreCubeFaceNormal A d ≫ serreCubeFace A b m i := by
  induction d generalizing b with
  | nil =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | point c d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change serreCubeFaceNormal A (cubeFaceNormalInsert d b i) ≫
        serreCubeFace A c _ 0 =
          (serreCubeFaceNormal A d ≫ serreCubeFace A c _ 0) ≫ serreCubeFace A b _ i.succ
      rw [ih b i]
      simp only [Category.assoc]
      rw [serreCubeFace_face_zero]
  | keep d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change (serreCubeFaceNormal A (cubeFaceNormalInsert d b i) ⊗ₘ
          𝟙 (serreIntervalComonoid A)) =
        (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeFace A b _ i ⊗ₘ 𝟙 (serreIntervalComonoid A))
      rw [ih b i]
      simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
