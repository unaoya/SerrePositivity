module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornLastTerm
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResidualIndexTransport

/-! # 最後の切断残差の次数と最後辺による後合成

概要：最後左切断の残差を欠面の標準残差へ、右切断を最後辺へ同定する。
方針：集合と次数の等式を異種等号へ渡し、通常順合成を輸送する。
規約：微分後の次数を明示する。使われ方：最後の Bianchi 寄与の評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}

/-- 最後左切断成分の次数は −n。 -/
lemma dgLastHornLastCut_left_degree (n : ℕ) :
    2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)).card : ℤ) = -(n : ℤ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_card]
  push_cast
  ring

/-- 最後右切断成分の次数は零。 -/
lemma dgLastHornLastCut_right_degree (n : ℕ) :
    2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n ≤ ·)).card : ℤ) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right]
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate, Fin.castSucc_ne_last]

variable (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2))

/-- 同じ欠面を標準端点・次数で評価した残差。 -/
def dgLastHornMissingResidualValue :=
  s.residual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n)

/-- 最後左切断の残差を、元の term の切断次数で評価する。 -/
def dgLastHornLastCutResidual :=
  s.residual (Finset.univ.filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)
    (2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)).card : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (Finset.mem_univ _) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n).le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max (Finset.mem_univ _) _) rfl

/-- 最後左切断の残差は、同じ欠面の標準残差。 -/
lemma dgLastHornLastCutResidual_heq :
    HEq (dgLastHornLastCutResidual s) (dgLastHornMissingResidualValue s) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexResidual_heq_of_indices_degree s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_left n) rfl rfl
    (dgLastHornLastCut_left_degree n)

/-- 最後右切断の元の斉次成分は、同じ実最後辺成分。 -/
lemma dgLastHornLastRightCut_heq :
    HEq (s.cutRight Finset.univ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Finset.mem_univ _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n))
      (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) :=
  s.hom_heq_of_indices_degree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right n) rfl rfl
    (dgLastHornLastCut_right_degree n)

/-- 最後辺による欠面残差の後合成を、微分した最上位 rhs の同じ次数で読む。 -/
def dgLastHornLastResidualComposite :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1 + 1) :=
  compose A (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) (dgLastHornMissingResidualValue s) (by omega)

/-- 最後右切断と左残差の通常順合成は、同じ最後辺の標準残差後合成。 -/
lemma dgLastHornLastResidualCutComposite_eq :
    compose A (s.cutRight Finset.univ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Finset.mem_univ _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) (dgLastHornLastCutResidual s)
      (by rw [dgLastHornLastCut_left_degree, dgLastHornLastCut_right_degree]; omega) =
      dgLastHornLastResidualComposite s :=
  eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq rfl rfl rfl
    (congrArg (fun k : ℤ => k + 1) (dgLastHornLastCut_left_degree n))
    (dgLastHornLastCut_right_degree n) rfl _ _ _ _
    (dgLastHornLastRightCut_heq s) (dgLastHornLastCutResidual_heq s)
    (by rw [dgLastHornLastCut_left_degree, dgLastHornLastCut_right_degree]; omega) (by omega))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
