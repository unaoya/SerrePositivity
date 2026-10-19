module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochainFiller

/-! # 実四次最後ホーンの既知残差の微分整合性

概要：Q を解く前に、既知部分 K の微分を最後辺と欠面右辺 R の合成の負へ同定する。
方針：Bianchi の三つの内部頂点のうち、最後の左切断の残差だけを残す。
規約：dK = −f34 R。使われ方：Hom 後合成 cone の閉残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 既知の全真部分集合の方程式と欠面成分の零から、最上位右辺の微分を回収する。 -/
lemma dgFourSimplex_rhs_top_differential (s : SimplexData A D 4)
    (he : ∀ I, I ≠ Finset.univ → I ≠ {0, 1, 2, 3} → s.Equation I)
    (hQ : s.hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0) :
    differential A (s.rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide)) =
      -compose A (s.edgeHom 3 4 (by decide))
        (s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
        (by decide) := by
  have h₁ : s.residualContribution Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) 1
      (by decide) (by decide) (by decide) = 0 := by
    rw [s.residualContribution_of_cuts _ _ _ _ _ _ _ _ _ _ _ _
      (he _ (by decide) (by decide)) (he _ (by decide) (by decide)),
      s.residual_zero_of_equation _ (he _ (by decide) (by decide)), smul_zero]
  have h₂ : s.residualContribution Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) 2
      (by decide) (by decide) (by decide) = 0 := by
    rw [s.residualContribution_of_cuts _ _ _ _ _ _ _ _ _ _ _ _
      (he _ (by decide) (by decide)) (he _ (by decide) (by decide)),
      s.residual_zero_of_equation _ (he _ (by decide) (by decide)), smul_zero]
  have hE : s.residual {0, 1, 2, 4} 0 4 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
    s.residual_zero_of_equation _ (he _ (by decide) (by decide)) _ _ _ _ _ _ _
  have hR : s.residual {3, 4} 3 4 0
      (by decide) (by decide) (by decide) (by decide) = 0 :=
    s.residual_zero_of_equation _ (he _ (by decide) (by decide)) _ _ _ _ _ _ _
  have hL : s.residual {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) =
      -s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) := by
    rw [SimplexData.residual, hQ]
    simp only [differential, map_zero, zero_sub]
  have h₃ : s.residualContribution Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) 3
      (by decide) (by decide) (by decide) =
      -compose A (s.edgeHom 3 4 (by decide))
        (s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
        (by decide) := by
    have hErase : (Finset.univ : Finset (Fin 5)).erase 3 = {0, 1, 2, 4} := by decide
    have hLeft : (Finset.univ : Finset (Fin 5)).filter (· ≤ 3) = {0, 1, 2, 3} := by decide
    have hRight : (Finset.univ : Finset (Fin 5)).filter (3 ≤ ·) = {3, 4} := by decide
    have hAbove : ((Finset.univ : Finset (Fin 5)).filter (3 < ·)).card = 1 := by decide
    simp only [SimplexData.residualContribution, Index.sign, hErase, hLeft, hRight, hAbove]
    change (-1 : ℤ) • (s.residual {0, 1, 2, 4} 0 4 (-2)
      (by decide) (by decide) (by decide) (by decide) -
      compose A (s.residual {3, 4} 3 4 0
        (by decide) (by decide) (by decide) (by decide))
        (s.hom {0, 1, 2, 3} 0 3 (-2)
          (by decide) (by decide) (by decide) (by decide)) (by decide) -
      (1 : ℤ) • compose A (s.edgeHom 3 4 (by decide))
        (s.residual {0, 1, 2, 3} 0 3 (-2)
          (by decide) (by decide) (by decide) (by decide)) (by decide)) = _
    rw [hE, hR, hL, zero_compose]
    simp only [zero_sub, neg_zero, one_smul, neg_neg, neg_smul]
    have hn := compose_sub_right (A := A) (k := -3 + 1 + 1) (s.edgeHom 3 4 (by decide))
      (0 : GradedHom A (s.obj 0) (s.obj 3) (-2 + 1))
      (s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
      (by decide)
    simpa only [zero_sub, compose_zero] using hn
  rw [s.bianchi]
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  norm_num [Fin.sum_univ_succ]
  exact (congrArg₂ (· + ·) h₁ (congrArg₂ (· + ·) h₂ h₃)).trans
    (by simp only [zero_add])

/-- 実四次最後ホーンの K・R は、最後辺を介した微分式を満たす。 -/
lemma dgFourLastHornTopResidual_differential
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) :
    differential A (dgFourLastHornTopResidual σ) =
      -compose A ((HornData.knownData σ).edgeHom 3 4 (by decide))
        (dgFourLastHornMissingResidual σ) (by decide) := by
  let s := HornData.knownData σ
  have hQ : s.hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 := by
    dsimp only [s, HornData.knownData]
    simp only [show ({0, 1, 2, 3} : Finset (Fin 5)) = Finset.univ.erase 4 from by decide,
      ne_eq, not_true_eq_false, ↓reduceDIte]
    split <;> rfl
  have he : ∀ I, I ≠ Finset.univ → I ≠ {0, 1, 2, 3} → s.Equation I := by
    intro I hf hm a b k hI ha hb hk
    exact HornData.knownData_equation σ I a b k hI ha hb hk hf
      (fun h => hm (h.trans (by decide)))
  have ht := dgFourSimplex_rhs_top s
  rw [hQ, compose_zero, add_zero] at ht
  exact (congrArg (fun f => differential A f) ht).symm.trans
    (dgFourSimplex_rhs_top_differential s he hQ)

end SerrePositivity.InfinityCategories
