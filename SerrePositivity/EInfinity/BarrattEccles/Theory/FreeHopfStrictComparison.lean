module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.StandardUnitAction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.StandardSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardExt

/-!
# 自由代数の指定 Hopf 比較と係数比較の厳密な一致

HA 3.2.4.7 の自由入力での比較。BS-W16 L16〜L18。
二つの指定射を元の複体の圏で比較し、既存の係数ホモトピー同値へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebra
variable (R : Type u) [CommRing R] (X Y : Complex R)

/-- 指定標準語上で、実際の Hopf 射は指定二色係数射と等しい。 -/
lemma freeStandardSource_hopfComparison (m n : ℕ)
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    freeStandardSource R X Y m n ≫ (freeHopfComparison (hopf R) h0 X Y).hom =
      freeStandardTarget R X Y m n := by
  rw [freeStandardSource_hopfComparison_arity]
  change _ ≫ hopfTensorAction (hopf R) ((operad R).freeAlgebra X)
    ((operad R).freeAlgebra Y) (m + n) = _
  dsimp only [hopfTensorAction]
  rw [whiskerLeft_comp_tensorHom_assoc]
  simp only [Category.assoc]
  erw [freeHopfComparisonInput_standard_separation]
  erw [tensorHom_def, Category.assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom, freeLeftUnitExtension_action, freeRightUnitExtension_action]
  erw [← tensorHom_comp_tensorHom, ← tensorμ_natural_left_assoc]
  simp only [freeStandardTarget, twoColorCoefficientComparison,
    comp_whiskerRight, Category.assoc]

/-- 二つの指定比較はホモトピー圏への移行前から同じ複体の射である。 -/
lemma freeHopfComparison_eq_coefficientComparison
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    (freeHopfComparison (hopf R) h0 X Y).hom =
      (freeSchurCoefficientHomotopyEquiv X Y).hom := by
  apply freeStandardSource_hom_ext R X Y
  intro m n
  rw [freeStandardSource_hopfComparison, freeStandardSource_coefficientComparison]

/-- 任意の入力複体について、実際の指定自由 Hopf 比較が擬同型である。 -/
lemma freeHopfComparison_quasiIso
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    QuasiIso (freeHopfComparison (hopf R) h0 X Y).hom := by
  rw [freeHopfComparison_eq_coefficientComparison]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
