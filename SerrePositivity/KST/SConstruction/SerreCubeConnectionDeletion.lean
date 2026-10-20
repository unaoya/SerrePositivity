module
public import SerrePositivity.KST.SConstruction.TensorRightDeletion
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxAbsorption
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionRelations
public import SerrePositivity.KST.SConstruction.SerreCubeDegeneracyRelations

/-! # 同じ座標の connection と退化
概要：connection の出力座標を削除すると、元の入力二座標を削除する射に一致する。
方針：右端の積の増大保存から始め、全座標へ tensor で帰納し、二つの削除順を回収する。
規約：元の Serre 余モノイド射の等号。使われ方：cubical connection と退化の混合関係式。
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

/-- 右端の connection の出力を削除する射は、右端二座標の二回の削除。 -/
lemma serreCubeConnection_degeneracy_zero (n : ℕ) :
    serreCubeConnection A n 0 ≫ serreCubeDegeneracy A n 0 =
      serreCubeDegeneracy A (n + 1) 0 ≫ serreCubeDegeneracy A n 0 := by
  rw [serreCubeConnection_zero_multiplication, serreCubeDegeneracy_zero,
    serreCubeDegeneracy_zero]
  change tensorRightMultiplication (serreCubeComonoid A n) (serreIntervalComonoid A) ≫
    ((𝟙 (serreCubeComonoid A n) ⊗ₘ serreIntervalAugmentationComonHom A) ≫
      (ρ_ (serreCubeComonoid A n)).hom) =
        ((𝟙 (serreCubeComonoid A n ⊗ serreIntervalComonoid A) ⊗ₘ
          serreIntervalAugmentationComonHom A) ≫
            (ρ_ (serreCubeComonoid A n ⊗ serreIntervalComonoid A)).hom) ≫ _
  simpa only [id_tensorHom, Category.assoc] using
    tensorRightMultiplication_deletion (serreCubeComonoid A n) (serreIntervalComonoid A)
      (serreIntervalAugmentationComonHom A) (serreIntervalMaxComonHom_augmentation A)

/-- 全座標で、connection の出力削除は元の二入力座標の二回の削除。 -/
lemma serreCubeConnection_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    serreCubeConnection A n i ≫ serreCubeDegeneracy A n i =
      serreCubeDegeneracy A (n + 1) i.castSucc ≫ serreCubeDegeneracy A n i := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeConnection_degeneracy_zero A 0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero] using serreCubeConnection_degeneracy_zero A (n + 1)
    · simp only [Fin.castSucc_succ, serreCubeConnection_succ, serreCubeDegeneracy_succ,
        tensorHom_comp_tensorHom, Category.comp_id]
      rw [ih]

/-- 同じ二入力座標を逆の順で削除しても、元の connection の出力削除を回収する。 -/
lemma serreCubeConnection_degeneracy_other (n : ℕ) (i : Fin (n + 1)) :
    serreCubeConnection A n i ≫ serreCubeDegeneracy A n i =
      serreCubeDegeneracy A (n + 1) i.succ ≫ serreCubeDegeneracy A n i :=
  (serreCubeConnection_degeneracy A n i).trans
    (serreCubeDegeneracy_degeneracy A n i i le_rfl).symm

end SerrePositivity.KST.SConstruction
