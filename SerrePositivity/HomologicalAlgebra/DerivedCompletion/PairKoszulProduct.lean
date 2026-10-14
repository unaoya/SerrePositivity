module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ProductCoordinates

/-! # 二座標Koszul塔の直積の行列表示 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 対の列を、二つの列の対へ並べ替える。 -/
def sequencePairEquiv : (ℕ → R × R) ≃ₗ[R] ((ℕ → R) × (ℕ → R)) where
  toFun x := (fun n ↦ (x n).1, fun n ↦ (x n).2)
  invFun x n := (x.1 n, x.2 n)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 二座標塔の直積。 -/
abbrev pairKoszulProduct (f d : R) := piObj (pairKoszulTower R f d)

/-- 二座標塔の直積の差分。 -/
abbrev pairKoszulDifference (f d : R) :=
  complexTowerDifference R (pairKoszulTower R f d) (pairKoszulTransition R f d)

/-- 直積の最低次数を列へ同定する。 -/
def pairKoszulProductNegTwoEquiv (f d : R) :
    (pairKoszulProduct R f d).X (-2) ≃ₗ[R] (ℕ → R) :=
  complexProductDegreeEquiv R _ (-2) ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageNegTwoEquiv R f d n)

/-- 直積の次数−1を二つの列へ同定する。 -/
def pairKoszulProductNegOneEquiv (f d : R) :
    (pairKoszulProduct R f d).X (-1) ≃ₗ[R] ((ℕ → R) × (ℕ → R)) :=
  complexProductDegreeEquiv R _ (-1) ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageNegOneEquiv R f d n) ≪≫ₗ
      sequencePairEquiv R

/-- 直積の零次数を列へ同定する。 -/
def pairKoszulProductZeroEquiv (f d : R) :
    (pairKoszulProduct R f d).X 0 ≃ₗ[R] (ℕ → R) :=
  complexProductDegreeEquiv R _ 0 ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageZeroEquiv R f d n)

@[simp] theorem pairKoszulProductNegTwoEquiv_apply (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) (n : ℕ) :
    pairKoszulProductNegTwoEquiv R f d x n = pairKoszulStageNegTwoEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-2) x n) := rfl

@[simp] theorem pairKoszulProductNegOneEquiv_fst (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) (n : ℕ) :
    (pairKoszulProductNegOneEquiv R f d x).1 n = (pairKoszulStageNegOneEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-1) x n)).1 := rfl

@[simp] theorem pairKoszulProductNegOneEquiv_snd (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) (n : ℕ) :
    (pairKoszulProductNegOneEquiv R f d x).2 n = (pairKoszulStageNegOneEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-1) x n)).2 := rfl

@[simp] theorem pairKoszulProductZeroEquiv_apply (f d : R)
    (x : (pairKoszulProduct R f d).X 0) (n : ℕ) :
    pairKoszulProductZeroEquiv R f d x n = pairKoszulStageZeroEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) 0 x n) := rfl

/-- 直積の最低次数の微分も、符号付きの交差境界。 -/
theorem pairKoszulProduct_d_negTwo (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) :
    pairKoszulProductNegOneEquiv R f d ((pairKoszulProduct R f d).d (-2) (-1) x) =
      (-principalPowerMap R f (pairKoszulProductNegTwoEquiv R f d x),
        principalPowerMap R d (pairKoszulProductNegTwoEquiv R f d x)) := by
  apply Prod.ext
  · funext n
    rw [pairKoszulProductNegOneEquiv_fst, complexProductDegreeEquiv_d,
      pairKoszulStage_d_negTwo]
    simp [principalPowerMap]
  · funext n
    rw [pairKoszulProductNegOneEquiv_snd, complexProductDegreeEquiv_d,
      pairKoszulStage_d_negTwo]
    rfl

/-- 直積の零次数への微分は、二つの冪による作用の和。 -/
theorem pairKoszulProduct_d_negOne (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) :
    pairKoszulProductZeroEquiv R f d ((pairKoszulProduct R f d).d (-1) 0 x) =
      principalPowerMap R d (pairKoszulProductNegOneEquiv R f d x).1 +
        principalPowerMap R f (pairKoszulProductNegOneEquiv R f d x).2 := by
  funext n
  rw [pairKoszulProductZeroEquiv_apply, complexProductDegreeEquiv_d, pairKoszulStage_d_negOne]
  rfl

/-- 直積の最低次数の差分はfdの漸化式。 -/
theorem pairKoszulProductNegTwo_difference (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) :
    pairKoszulProductNegTwoEquiv R f d ((pairKoszulDifference R f d).f (-2) x) =
      adicRecurrenceMap (f * d) (pairKoszulProductNegTwoEquiv R f d x) := by
  funext n
  rw [pairKoszulProductNegTwoEquiv_apply, complexProductDegreeEquiv_difference,
    map_sub, pairKoszulStageNegTwo_transition]
  rfl

/-- 直積の次数−1の差分は、dとfの二つの漸化式。 -/
theorem pairKoszulProductNegOne_difference (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) :
    pairKoszulProductNegOneEquiv R f d ((pairKoszulDifference R f d).f (-1) x) =
      (adicRecurrenceMap d (pairKoszulProductNegOneEquiv R f d x).1,
        adicRecurrenceMap f (pairKoszulProductNegOneEquiv R f d x).2) := by
  apply Prod.ext
  · funext n
    rw [pairKoszulProductNegOneEquiv_fst, complexProductDegreeEquiv_difference,
      map_sub, pairKoszulStageNegOne_transition]
    rfl
  · funext n
    rw [pairKoszulProductNegOneEquiv_snd, complexProductDegreeEquiv_difference,
      map_sub, pairKoszulStageNegOne_transition]
    rfl

/-- 直積の零次数の差分は恒等遷移の漸化式。 -/
theorem pairKoszulProductZero_difference (f d : R)
    (x : (pairKoszulProduct R f d).X 0) :
    pairKoszulProductZeroEquiv R f d ((pairKoszulDifference R f d).f 0 x) =
      adicRecurrenceMap (1 : R) (pairKoszulProductZeroEquiv R f d x) := by
  funext n
  rw [pairKoszulProductZeroEquiv_apply, complexProductDegreeEquiv_difference,
    map_sub, pairKoszulStageZero_transition]
  simp [adicRecurrenceMap]

/-- 直積は二座標Koszul複体の次数の範囲外では零。 -/
theorem pairKoszulProduct_isZero (f d : R) (i : ℤ) (hi : i < -2 ∨ 0 < i) :
    IsZero ((pairKoszulProduct R f d).X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ (complexProductDegreeEquiv R _ i).injective ?_⟩
  funext n
  have hn : IsZero ((pairKoszulTower R f d n).X i) := by
    rw [← powerKoszulTower_pair_eq]
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt _ i (by simpa using hi)
    · exact koszulComplex_isZero_X_of_pos _ i hi
  exact (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _

end SerrePositivity.DerivedCompletion
