module
public import SerrePositivity.KST.SConstruction.SerreCubePrefixNaturality
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateRetractions

/-! # 全座標の元の面・退化の混合関係
概要：異なる二座標の端点挿入と削除は、両方向で cubical な添字関係を満たす。
方針：左側の任意の射に関する右端の自然性を基底に、両座標を内側へ tensor で移す。
規約：同じ座標の関係は既存の厳密な退縮。使われ方：cubical 圏の面・退化の作用。
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

/-- 右端の挿入と内側の削除は、元の順序を変えて同じ射になる。 -/
lemma serreCubeFace_degeneracy_right_zero (b : Bool) (n : ℕ) (j : Fin (n + 1)) :
    serreCubeFace A b (n + 1) 0 ≫ serreCubeDegeneracy A (n + 1) j.succ =
      serreCubeDegeneracy A n j ≫ serreCubeFace A b n 0 := by
  rw [serreCubeDegeneracy_succ]
  exact (serreCubeFace_zero_naturality A b (serreCubeDegeneracy A n j)).symm

/-- 内側の挿入と右端の削除も、元の順序を変えて同じ射になる。 -/
lemma serreCubeFace_degeneracy_left_zero (b : Bool) (n : ℕ) (j : Fin (n + 1)) :
    serreCubeFace A b (n + 1) j.succ ≫ serreCubeDegeneracy A (n + 1) 0 =
      serreCubeDegeneracy A n 0 ≫ serreCubeFace A b n j := by
  rw [serreCubeFace_succ]
  exact serreCubeDegeneracy_zero_naturality A (serreCubeFace A b n j)

/-- 挿入座標が右側にある全ての場合の、元の面・退化の交換関係。 -/
lemma serreCubeFace_degeneracy_right (b : Bool) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeFace A b (n + 1) i.castSucc ≫ serreCubeDegeneracy A (n + 1) j.succ =
      serreCubeDegeneracy A n j ≫ serreCubeFace A b n i := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact serreCubeFace_degeneracy_right_zero A b 0 0
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using serreCubeFace_degeneracy_right_zero A b (n + 1) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeFace A b (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeDegeneracy A (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeDegeneracy A n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeFace A b n i ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          ih i j (Fin.succ_le_succ_iff.mp h)]

/-- 挿入座標が左側にある全ての場合の、元の面・退化の交換関係。 -/
lemma serreCubeFace_degeneracy_left (b : Bool) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeFace A b (n + 1) j.succ ≫ serreCubeDegeneracy A (n + 1) i.castSucc =
      serreCubeDegeneracy A n i ≫ serreCubeFace A b n j := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact serreCubeFace_degeneracy_left_zero A b 0 0
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using serreCubeFace_degeneracy_left_zero A b (n + 1) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeFace A b (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeDegeneracy A (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeDegeneracy A n i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeFace A b n j ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          ih i j (Fin.succ_le_succ_iff.mp h)]

end SerrePositivity.KST.SConstruction
