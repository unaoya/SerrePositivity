module
public import SerrePositivity.KST.SConstruction.SerreCubePrefixNaturality

/-! # 元の鎖立方体の全ての退化の交換関係
概要：元の増大による二座標の削除は、全次元で cubical な添字関係を満たす。
方針：右端の削除の自然性を基底に、内側は tensor の関手性で帰納する。
規約：座標は右端から数える。使われ方：cubical 圏の退化による作用の束ね。
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

/-- 任意の内側の削除と右端の削除は、元の添字のずれを保って交換する。 -/
lemma serreCubeDegeneracy_degeneracy_zero (n : ℕ) (j : Fin (n + 1)) :
    serreCubeDegeneracy A (n + 1) j.succ ≫ serreCubeDegeneracy A n 0 =
      serreCubeDegeneracy A (n + 1) 0 ≫ serreCubeDegeneracy A n j := by
  rw [serreCubeDegeneracy_succ]
  exact serreCubeDegeneracy_zero_naturality A (serreCubeDegeneracy A n j)

/-- 全次元の順序づけた二座標で、元の退化の交換関係が厳密に成立する。 -/
lemma serreCubeDegeneracy_degeneracy (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    serreCubeDegeneracy A (n + 1) j.succ ≫ serreCubeDegeneracy A n i =
      serreCubeDegeneracy A (n + 1) i.castSucc ≫ serreCubeDegeneracy A n j := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact serreCubeDegeneracy_degeneracy_zero A 0 0
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simpa only [Fin.castSucc_zero] using serreCubeDegeneracy_degeneracy_zero A (n + 1) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((not_le_of_gt (Fin.succ_pos i)) h)
      · intro h
        change ((serreCubeDegeneracy A (n + 1) j.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeDegeneracy A n i ⊗ₘ 𝟙 (serreIntervalComonoid A))) =
            (serreCubeDegeneracy A (n + 1) i.castSucc ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeDegeneracy A n j ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          ih i j (Fin.succ_le_succ_iff.mp h)]

end SerrePositivity.KST.SConstruction
