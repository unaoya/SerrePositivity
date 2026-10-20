module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxMonoid
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateRetractions
public import SerrePositivity.KST.SConstruction.TensorRightMultiplication

/-! # 隣接 connection の全座標の結合関係
概要：右端の max 積の結合単位則を、全鎖立方体の隣接 connection へ移す。
方針：右端を抽象 monoidal 補題で処理し、内側の座標は tensor の関手性で帰納する。
規約：座標は右端から数え、元の余モノイド射の厳密な等号を保つ。
使われ方：cubical connection と面の関係式。
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

/-- 右端の元の connection は、同じ Serre 余モノイドの max 積。 -/
lemma serreCubeConnection_zero_multiplication (n : ℕ) :
    serreCubeConnection A n 0 =
      tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) := by
  rw [serreCubeConnection_zero]
  simp only [tensorRightMultiplication, id_tensorHom]
  rfl

/-- 右端の隣接三座標の二つの結合順は、同じ元の connection の反復。 -/
lemma serreCubeConnection_zero_assoc (n : ℕ) :
    serreCubeConnection A (n + 1) 0 ≫ serreCubeConnection A n 0 =
      serreCubeConnection A (n + 1) (0 : Fin (n + 1)).succ ≫ serreCubeConnection A n 0 := by
  rw [serreCubeConnection_succ]
  simp only [serreCubeConnection_zero_multiplication, tensorHom_id]
  exact tensorRightMultiplication_assoc (serreCubeComonoid A n) (serreIntervalComonoid A)

/-- 右端への零端点挿入と connection は、同じ元の恒等射。 -/
lemma serreCubeFace_zero_connection_right (n : ℕ) :
    serreCubeFace A false (n + 1) 0 ≫ serreCubeConnection A n 0 =
      𝟙 (serreCubeComonoid A (n + 1)) := by
  rw [serreCubeFace_zero, serreCubeConnection_zero_multiplication]
  change (ρ_ (serreCubeComonoid A n ⊗ serreIntervalComonoid A)).inv ≫
    (𝟙 (serreCubeComonoid A n ⊗ serreIntervalComonoid A) ⊗ₘ MonObj.one) ≫
      tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) = 𝟙 _
  simpa only [id_tensorHom] using
    tensorRightMultiplication_right_unit (serreCubeComonoid A n) (serreIntervalComonoid A)

/-- 右から二番目への零端点挿入と connection も、同じ元の恒等射。 -/
lemma serreCubeFace_zero_connection_left (n : ℕ) :
    serreCubeFace A false (n + 1) (0 : Fin (n + 1)).succ ≫ serreCubeConnection A n 0 =
      𝟙 (serreCubeComonoid A (n + 1)) := by
  rw [serreCubeFace_succ, serreCubeFace_zero, serreCubeConnection_zero_multiplication]
  change (((ρ_ (serreCubeComonoid A n)).inv ≫
    (𝟙 (serreCubeComonoid A n) ⊗ₘ MonObj.one)) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) = 𝟙 _
  simpa only [id_tensorHom, tensorHom_id] using
    tensorRightMultiplication_left_unit (serreCubeComonoid A n) (serreIntervalComonoid A)

/-- 任意の隣接三座標で、元の max connection の二つの結合順が厳密に一致する。 -/
lemma serreCubeConnection_assoc (n : ℕ) (i : Fin (n + 1)) :
    serreCubeConnection A (n + 1) i.castSucc ≫ serreCubeConnection A n i =
      serreCubeConnection A (n + 1) i.succ ≫ serreCubeConnection A n i := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeConnection_zero_assoc A 0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero] using serreCubeConnection_zero_assoc A (n + 1)
    · simp only [Fin.castSucc_succ, serreCubeConnection_succ, tensorHom_comp_tensorHom,
        Category.comp_id]
      rw [ih]
      rfl

/-- 全座標で、結合する二座標の右側への零端点挿入は connection の切断。 -/
lemma serreCubeFace_connection_right (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A false (n + 1) i.castSucc ≫ serreCubeConnection A n i =
      𝟙 (serreCubeComonoid A (n + 1)) := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeFace_zero_connection_right A 0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero] using serreCubeFace_zero_connection_right A (n + 1)
    · simp only [Fin.castSucc_succ, serreCubeFace_succ, serreCubeConnection_succ,
        tensorHom_comp_tensorHom, Category.comp_id]
      rw [ih]
      simp only [tensorHom_id, id_whiskerRight]
      rfl

/-- 全座標で、結合する二座標の左側への零端点挿入も connection の切断。 -/
lemma serreCubeFace_connection_left (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A false (n + 1) i.succ ≫ serreCubeConnection A n i =
      𝟙 (serreCubeComonoid A (n + 1)) := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeFace_zero_connection_left A 0
  | succ n ih =>
    refine Fin.cases (serreCubeFace_zero_connection_left A (n + 1)) (fun j => ?_) i
    change ((serreCubeFace A false (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeConnection A n j ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
        𝟙 (serreCubeComonoid A (n + 1) ⊗ serreIntervalComonoid A)
    rw [tensorHom_comp_tensorHom, ih]
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight]

end SerrePositivity.KST.SConstruction
