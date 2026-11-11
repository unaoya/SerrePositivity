module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornResidualCutComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornKnownCutEquations

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}

/-- 最後内部頂点の Bianchi の外側符号は負一。 -/
lemma dgLastHornLastCut_sign (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (Finset.univ : Finset (Fin (n + 3))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) = (-1 : ℤˣ) := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_upper_card]

/-- 最後右切断の零次数の Leibniz 符号は正一。 -/
lemma dgLastHornLastCut_right_sign (n : ℕ) :
    (2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n ≤ ·)).card : ℤ)).negOnePow = (1 : ℤˣ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right_degree]
  rfl

variable (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2))

/-- 微分した最上位 rhs の最後内部頂点の寄与。 -/
def dgLastHornLastResidualTerm :=
  s.residualContribution Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)

/-- 右切断・削除の方程式の下で、最後の寄与は最後辺による左残差の後合成。 -/
lemma dgLastHornLastResidualTerm_formula
    (hE : s.Equation (Finset.univ.erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)))
    (hR : s.Equation (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n ≤ ·))) :
    dgLastHornLastResidualTerm s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastResidualComposite s := by
  unfold dgLastHornLastResidualTerm _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.residual_zero_of_equation s _ hE,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.residual_zero_of_equation s _ hR, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero, zero_sub]
  rw [dgLastHornLastCut_sign, dgLastHornLastCut_right_sign]
  change (-1 : ℤ) • (-((1 : ℤ) • (_root_.SerrePositivity.DifferentialGraded.compose A
    (s.cutRight Finset.univ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCutResidual s)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_left_degree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right_degree]; omega)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastResidualCutComposite_eq]
  simp only [one_smul, neg_smul, neg_neg]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
