module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornResidualCutComponents
public import SerrePositivity.InfinityCategories.Derived.DGLastHornKnownCutEquations

/-! # 一般 Bianchi の最後の一寄与

概要：最後の右切断・削除方程式の下で、残る寄与は最後辺による欠面残差の後合成。
方針：二つの既知残差を零にし、二つの符号と切断合成の次数を照合する。
規約：左残差の零は仮定しない。使われ方：dK と欠面残差 R の一般整合式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}

/-- 最後内部頂点の Bianchi の外側符号は負一。 -/
lemma dgLastHornLastCut_sign (n : ℕ) :
    Index.sign (Finset.univ : Finset (Fin (n + 3))) (dgLastHornPenultimate n) = (-1 : ℤˣ) := by
  simp [Index.sign, dgLastHornLastCut_upper_card]

/-- 最後右切断の零次数の Leibniz 符号は正一。 -/
lemma dgLastHornLastCut_right_sign (n : ℕ) :
    (2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (dgLastHornPenultimate n ≤ ·)).card : ℤ)).negOnePow = (1 : ℤˣ) := by
  rw [dgLastHornLastCut_right_degree]
  rfl

variable (s : SimplexData A D (n + 2))

/-- 微分した最上位 rhs の最後内部頂点の寄与。 -/
def dgLastHornLastResidualTerm :=
  s.residualContribution Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)
    (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_pos n)
    (dgLastHornPenultimate_lt_last n)

/-- 右切断・削除の方程式の下で、最後の寄与は最後辺による左残差の後合成。 -/
lemma dgLastHornLastResidualTerm_formula
    (hE : s.Equation (Finset.univ.erase (dgLastHornPenultimate n)))
    (hR : s.Equation (Finset.univ.filter (dgLastHornPenultimate n ≤ ·))) :
    dgLastHornLastResidualTerm s = dgLastHornLastResidualComposite s := by
  unfold dgLastHornLastResidualTerm SimplexData.residualContribution
  simp only [SimplexData.residual_zero_of_equation s _ hE,
    SimplexData.residual_zero_of_equation s _ hR, zero_compose, sub_zero, zero_sub]
  rw [dgLastHornLastCut_sign, dgLastHornLastCut_right_sign]
  change (-1 : ℤ) • (-((1 : ℤ) • (compose A
    (s.cutRight Finset.univ (Fin.last (n + 2)) (dgLastHornTop_two n) (dgLastHornTop_max n)
      (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_lt_last n))
    (dgLastHornLastCutResidual s)
    (by rw [dgLastHornLastCut_left_degree, dgLastHornLastCut_right_degree]; omega)))) = _
  rw [dgLastHornLastResidualCutComposite_eq]
  simp only [one_smul, neg_smul, neg_neg]

end SerrePositivity.InfinityCategories
