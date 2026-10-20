module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornLastResidualTerm

/-! # 一般最後外ホーンの二残差の Bianchi 整合式

概要：元の既知最上位残差 K の微分は、最後辺による欠面右辺 R の後合成の負。
方針：Bianchi の最後以外の寄与を既知方程式で消し、最後の左残差を −R と読む。
規約：二未知解の存在を仮定しない。使われ方：一般 Hom cone の閉残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 最後辺による R の後合成を、微分した K と同じ次数で読む。 -/
def dgGeneralLastHornPostcomposeR :
    GradedHom A ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1 + 1) :=
  compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
    (dgLastHornPenultimate_lt_last n)) (dgGeneralLastHornMissingResidual σ) (by omega)

/-- 元の既知データの欠面残差は、未知成分が零なので同じ R の負。 -/
lemma dgGeneralLastHornKnown_missingResidual :
    dgLastHornMissingResidualValue (HornData.knownData σ) =
      -dgGeneralLastHornMissingResidual σ := by
  unfold dgLastHornMissingResidualValue SimplexData.residual
  rw [dgGeneralLastHornMissingHom_zero]
  simp only [differential, map_zero, zero_sub]
  rfl

/-- 元の最後辺による欠面残差の後合成は、同じ R 後合成の負。 -/
lemma dgGeneralLastHornKnown_lastResidualComposite :
    dgLastHornLastResidualComposite (HornData.knownData σ) =
      -dgGeneralLastHornPostcomposeR σ := by
  unfold dgLastHornLastResidualComposite dgGeneralLastHornPostcomposeR
  rw [dgGeneralLastHornKnown_missingResidual]
  simp only [compose, forward, TensorProduct.neg_tmul, map_neg, smul_neg]

/-- 最後以外の内部頂点の Bianchi 寄与は、既知方程式だけから零となる。 -/
lemma dgGeneralLastHornResidualContribution_zero (j : Fin (n + 3))
    (h₀ : (0 : Fin (n + 3)) < j) (hj : j < Fin.last (n + 2))
    (hne : j ≠ dgLastHornPenultimate n) :
    (HornData.knownData σ).residualContribution Finset.univ 0 (Fin.last (n + 2))
      (-(n : ℤ) - 1) (dgLastHornTop_two n) (dgLastHornTop_min n) (dgLastHornTop_max n)
      (dgLastHornTop_degree n) j (Finset.mem_univ _) h₀ hj = 0 := by
  rw [SimplexData.residualContribution_of_cuts _ _ _ _ _ _ _ _ _ _ _ _ _
    (dgGeneralLastHornKnown_leftCut σ j hj hne) (dgGeneralLastHornKnown_rightCut σ j h₀ hj)]
  rw [SimplexData.residual_zero_of_equation _ _ (dgGeneralLastHornKnown_erase σ j hj)]
  exact smul_zero _

/-- 最後の Bianchi 寄与は、最後辺による R の後合成の負。 -/
lemma dgGeneralLastHornLastResidualTerm :
    dgLastHornLastResidualTerm (HornData.knownData σ) = -dgGeneralLastHornPostcomposeR σ :=
  (dgLastHornLastResidualTerm_formula (HornData.knownData σ)
    (dgGeneralLastHornKnown_erase σ _ (dgLastHornPenultimate_lt_last n))
    (dgGeneralLastHornKnown_rightCut σ _ (dgLastHornPenultimate_pos n)
      (dgLastHornPenultimate_lt_last n))).trans (dgGeneralLastHornKnown_lastResidualComposite σ)

/-- 二未知の元の残差は、全次元で dK＝−最後辺∘R を満たす。 -/
lemma dgGeneralLastHornTopResidual_differential :
    differential A (dgGeneralLastHornTopResidual σ) = -dgGeneralLastHornPostcomposeR σ := by
  unfold dgGeneralLastHornTopResidual dgLastHornTopRhs
  rw [SimplexData.bianchi, Finset.sum_eq_single
    (⟨dgLastHornPenultimate n, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (n + 3))))]
  · simp only [dite_eq_left (show (0 : Fin (n + 3)) < dgLastHornPenultimate n ∧
      dgLastHornPenultimate n < Fin.last (n + 2) from
        ⟨dgLastHornPenultimate_pos n, dgLastHornPenultimate_lt_last n⟩)]
    exact dgGeneralLastHornLastResidualTerm σ
  · intro j _ hj
    by_cases hi : (0 : Fin (n + 3)) < j.val ∧ j.val < Fin.last (n + 2)
    · simp only [dite_eq_left hi]
      exact dgGeneralLastHornResidualContribution_zero σ j.val hi.1 hi.2
        (fun he => hj (Subtype.ext he))
    · simp only [dite_eq_right hi]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end SerrePositivity.InfinityCategories
