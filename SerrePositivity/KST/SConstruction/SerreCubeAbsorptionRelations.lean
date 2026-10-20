module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxAbsorption
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionRelations
public import SerrePositivity.KST.SConstruction.TensorRightAbsorption

/-! # 全座標の一端点の面と connection の吸収関係
概要：一端点挿入と connection の合成は、元の座標の削除と一端点挿入になる。
方針：右端の左右吸収を monoidal な式で処理し、内側の全座標へ tensor で帰納する。
規約：座標は右端から数える。使われ方：元の Serre 鎖立方体の cubical 関係式。
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

/-- 右端への一端点の挿入と connection は、元の削除と一端点の挿入に等しい。 -/
lemma serreCubeFace_one_connection_right_zero (n : ℕ) :
    serreCubeFace A true (n + 1) 0 ≫ serreCubeConnection A n 0 =
      serreCubeDegeneracy A n 0 ≫ serreCubeFace A true n 0 := by
  rw [serreCubeFace_zero, serreCubeConnection_zero_multiplication,
    serreCubeDegeneracy_zero, serreCubeFace_zero]
  dsimp only [serreIntervalEndpointComonHom]
  simp only [ite_true]
  change (ρ_ (serreCubeComonoid A n ⊗ serreIntervalComonoid A)).inv ≫
    (𝟙 (serreCubeComonoid A n ⊗ serreIntervalComonoid A) ⊗ₘ serreIntervalOneComonHom A) ≫
      tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) = _
  simpa only [id_tensorHom, Category.assoc] using
    tensorRightMultiplication_right_absorption (serreCubeComonoid A n)
      (serreIntervalComonoid A) (serreIntervalOneComonHom A)
      (serreIntervalAugmentationComonHom A) (serreIntervalMaxComonHom_right_absorption A)

/-- 右から二番目への一端点の挿入と connection も、同じ削除と挿入になる。 -/
lemma serreCubeFace_one_connection_left_zero (n : ℕ) :
    serreCubeFace A true (n + 1) (0 : Fin (n + 1)).succ ≫ serreCubeConnection A n 0 =
      serreCubeDegeneracy A n 0 ≫ serreCubeFace A true n 0 := by
  rw [serreCubeFace_succ, serreCubeFace_zero, serreCubeConnection_zero_multiplication,
    serreCubeDegeneracy_zero]
  dsimp only [serreIntervalEndpointComonHom]
  simp only [ite_true]
  change (((ρ_ (serreCubeComonoid A n)).inv ≫
    (𝟙 (serreCubeComonoid A n) ⊗ₘ serreIntervalOneComonHom A)) ⊗ₘ
      𝟙 (serreIntervalComonoid A)) ≫
        tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) = _
  simpa only [id_tensorHom, tensorHom_id, Category.assoc] using
    tensorRightMultiplication_left_absorption (serreCubeComonoid A n)
      (serreIntervalComonoid A) (serreIntervalOneComonHom A)
      (serreIntervalAugmentationComonHom A) (serreIntervalMaxComonHom_left_absorption A)

/-- 全座標の右側の一端点挿入と connection は、元の削除と一端点挿入を回収する。 -/
lemma serreCubeFace_one_connection_right (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A true (n + 1) i.castSucc ≫ serreCubeConnection A n i =
      serreCubeDegeneracy A n i ≫ serreCubeFace A true n i := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeFace_one_connection_right_zero A 0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero] using serreCubeFace_one_connection_right_zero A (n + 1)
    · simp only [Fin.castSucc_succ, serreCubeFace_succ, serreCubeDegeneracy_succ,
        serreCubeConnection_succ, tensorHom_comp_tensorHom, Category.comp_id]
      rw [ih]

/-- 全座標の左側の一端点挿入と connection も、元の削除と一端点挿入を回収する。 -/
lemma serreCubeFace_one_connection_left (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A true (n + 1) i.succ ≫ serreCubeConnection A n i =
      serreCubeDegeneracy A n i ≫ serreCubeFace A true n i := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeFace_one_connection_left_zero A 0
  | succ n ih =>
    refine Fin.cases (serreCubeFace_one_connection_left_zero A (n + 1)) (fun j => ?_) i
    change ((serreCubeFace A true (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeConnection A n j ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
        (serreCubeDegeneracy A n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeFace A true n j ⊗ₘ 𝟙 (serreIntervalComonoid A))
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ih]

end SerrePositivity.KST.SConstruction
