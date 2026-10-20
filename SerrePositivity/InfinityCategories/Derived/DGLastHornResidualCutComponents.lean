module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornLastTerm
public import SerrePositivity.InfinityCategories.Derived.DGResidualIndexTransport

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
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}

/-- 最後左切断成分の次数は −n。 -/
lemma dgLastHornLastCut_left_degree (n : ℕ) :
    2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (· ≤ dgLastHornPenultimate n)).card : ℤ) = -(n : ℤ) := by
  rw [dgLastHornLastCut_left, dgLastHornMissingIndex_card]
  push_cast
  ring

/-- 最後右切断成分の次数は零。 -/
lemma dgLastHornLastCut_right_degree (n : ℕ) :
    2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (dgLastHornPenultimate n ≤ ·)).card : ℤ) = 0 := by
  rw [dgLastHornLastCut_right]
  simp [dgLastHornPenultimate, Fin.castSucc_ne_last]

variable (s : SimplexData A D (n + 2))

/-- 同じ欠面を標準端点・次数で評価した残差。 -/
def dgLastHornMissingResidualValue :=
  s.residual (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
    (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)

/-- 最後左切断の残差を、元の term の切断次数で評価する。 -/
def dgLastHornLastCutResidual :=
  s.residual (Finset.univ.filter (· ≤ dgLastHornPenultimate n)) 0 (dgLastHornPenultimate n)
    (2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (· ≤ dgLastHornPenultimate n)).card : ℤ))
    (Index.left_two (Finset.mem_univ _) (Finset.mem_univ _) (dgLastHornPenultimate_pos n))
    (Index.left_min ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
      (dgLastHornPenultimate_pos n).le _) (Index.left_max (Finset.mem_univ _) _) rfl

/-- 最後左切断の残差は、同じ欠面の標準残差。 -/
lemma dgLastHornLastCutResidual_heq :
    HEq (dgLastHornLastCutResidual s) (dgLastHornMissingResidualValue s) :=
  dgSimplexResidual_heq_of_indices_degree s (dgLastHornLastCut_left n) rfl rfl
    (dgLastHornLastCut_left_degree n)

/-- 最後右切断の元の斉次成分は、同じ実最後辺成分。 -/
lemma dgLastHornLastRightCut_heq :
    HEq (s.cutRight Finset.univ (Fin.last (n + 2)) (dgLastHornTop_two n)
      (dgLastHornTop_max n) (dgLastHornPenultimate n) (Finset.mem_univ _)
      (dgLastHornPenultimate_lt_last n))
      (s.edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n)) :=
  s.hom_heq_of_indices_degree (dgLastHornLastCut_right n) rfl rfl
    (dgLastHornLastCut_right_degree n)

/-- 最後辺による欠面残差の後合成を、微分した最上位 rhs の同じ次数で読む。 -/
def dgLastHornLastResidualComposite :
    GradedHom A (s.obj 0) (s.obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1 + 1) :=
  compose A (s.edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
    (dgLastHornPenultimate_lt_last n)) (dgLastHornMissingResidualValue s) (by omega)

/-- 最後右切断と左残差の通常順合成は、同じ最後辺の標準残差後合成。 -/
lemma dgLastHornLastResidualCutComposite_eq :
    compose A (s.cutRight Finset.univ (Fin.last (n + 2)) (dgLastHornTop_two n)
      (dgLastHornTop_max n) (dgLastHornPenultimate n) (Finset.mem_univ _)
      (dgLastHornPenultimate_lt_last n)) (dgLastHornLastCutResidual s)
      (by rw [dgLastHornLastCut_left_degree, dgLastHornLastCut_right_degree]; omega) =
      dgLastHornLastResidualComposite s :=
  eq_of_heq (gradedHom_compose_heq rfl rfl rfl
    (congrArg (fun k : ℤ => k + 1) (dgLastHornLastCut_left_degree n))
    (dgLastHornLastCut_right_degree n) rfl _ _ _ _
    (dgLastHornLastRightCut_heq s) (dgLastHornLastCutResidual_heq s)
    (by rw [dgLastHornLastCut_left_degree, dgLastHornLastCut_right_degree]; omega) (by omega))

end SerrePositivity.InfinityCategories
