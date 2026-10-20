module
public import SerrePositivity.KST.SConstruction.SerreCubePrefixNaturality

/-! # 離れた面と connection の交換関係
概要：離れた座標の元の操作は、全次元・全座標で cubical な添字関係を満たす。
方針：任意の左側の射に関する右端の自然性を基底に、tensor の関手性で帰納する。
規約：座標は右端から数える。使われ方：connection を持つ cubical 圏の作用の束ね。
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

/-- 右端を含む離れた二操作は、元の添字を保って厳密に交換する。 -/
lemma serreCubeFace_connection_right_far_zero (b : Bool) (n : ℕ) (j : Fin (n + 1)) :
    serreCubeFace A b (n + 2) 0 ≫ serreCubeConnection A (n + 1) j.succ =
      serreCubeConnection A n j ≫ serreCubeFace A b (n + 1) 0 := by
  rw [serreCubeConnection_succ]
  exact (serreCubeFace_zero_naturality A b (serreCubeConnection A n j)).symm

/-- 全次元の離れた二座標で、元の二操作の交換関係が厳密に成立する。 -/
lemma serreCubeFace_connection_right_far (b : Bool) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeFace A b (n + 2) i.castSucc.castSucc ≫ serreCubeConnection A (n + 1) j.succ =
      serreCubeConnection A n j ≫ serreCubeFace A b (n + 1) i.castSucc := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact serreCubeFace_connection_right_far_zero A b 0 0
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using serreCubeFace_connection_right_far_zero A b (n + 1) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeFace A b (n + 2) i.castSucc.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeConnection A (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeConnection A n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeFace A b (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          ih i j (Fin.succ_le_succ_iff.mp h)]

/-- 右端を含む離れた二操作は、元の添字を保って厳密に交換する。 -/
lemma serreCubeFace_connection_left_far_zero (b : Bool) (n : ℕ) (j : Fin (n + 1)) :
    serreCubeFace A b (n + 2) j.succ.succ ≫ serreCubeConnection A (n + 1) 0 =
      serreCubeConnection A n 0 ≫ serreCubeFace A b (n + 1) j.succ := by
  simp only [serreCubeFace_succ, serreCubeConnection_zero,
    tensorHom_id, id_tensorHom, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange]

/-- 全次元の離れた二座標で、元の二操作の交換関係が厳密に成立する。 -/
lemma serreCubeFace_connection_left_far (b : Bool) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeFace A b (n + 2) j.succ.succ ≫ serreCubeConnection A (n + 1) i.castSucc =
      serreCubeConnection A n i ≫ serreCubeFace A b (n + 1) j.succ := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact serreCubeFace_connection_left_far_zero A b 0 0
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using serreCubeFace_connection_left_far_zero A b (n + 1) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeFace A b (n + 2) j.succ.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeConnection A (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeConnection A n i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeFace A b (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          ih i j (Fin.succ_le_succ_iff.mp h)]

end SerrePositivity.KST.SConstruction
