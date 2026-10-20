module
public import SerrePositivity.KST.SConstruction.SerreCubePrefixNaturality

/-! # 元の鎖立方体の全ての面の交換関係
概要：元の二端点の面は、任意の次元・任意の順序づけた二座標で厳密に交換する。
方針：右端の自然性を基底とし、両座標が内側なら tensor の関手性で帰納する。
規約：座標は右端から数える。使われ方：cubical 圏の面による作用の束ね。
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

/-- 任意の面と右端の面は、元の添字のずれを保って交換する。 -/
lemma serreCubeFace_face_zero (b c : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A b n i ≫ serreCubeFace A c (n + 1) 0 =
      serreCubeFace A c n 0 ≫ serreCubeFace A b (n + 1) i.succ := by
  rw [serreCubeFace_succ]
  exact serreCubeFace_zero_naturality A c (serreCubeFace A b n i)

/-- 全次元・全ての両端点で、元の面の二座標の交換関係が厳密に成立する。 -/
lemma serreCubeFace_face (b c : Bool) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeFace A b n i ≫ serreCubeFace A c (n + 1) j.succ =
      serreCubeFace A c n j ≫ serreCubeFace A b (n + 1) i.castSucc := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact (serreCubeFace_face_zero A c b 0 0).symm
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using (serreCubeFace_face_zero A c b (n + 1) j).symm
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeFace A b n i ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeFace A c (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeFace A c n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeFace A b (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ih i j (Fin.succ_le_succ_iff.mp h)]

end SerrePositivity.KST.SConstruction
