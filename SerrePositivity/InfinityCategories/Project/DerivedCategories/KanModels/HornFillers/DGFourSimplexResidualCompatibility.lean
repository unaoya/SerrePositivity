module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornCochainFiller

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 既知の全真部分集合の方程式と欠面成分の零から、最上位右辺の微分を回収する。 -/
lemma dgFourSimplex_rhs_top_differential (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4)
    (he : ∀ I, I ≠ Finset.univ → I ≠ {0, 1, 2, 3} → s.Equation I)
    (hQ : s.hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (s.rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide)) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 3 4 (by decide))
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
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.residual, hQ]
    simp only [_root_.SerrePositivity.DifferentialGraded.differential, map_zero, zero_sub]
  have h₃ : s.residualContribution Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) 3
      (by decide) (by decide) (by decide) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 3 4 (by decide))
        (s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
        (by decide) := by
    have hErase : (Finset.univ : Finset (Fin 5)).erase 3 = {0, 1, 2, 4} := by decide
    have hLeft : (Finset.univ : Finset (Fin 5)).filter (· ≤ 3) = {0, 1, 2, 3} := by decide
    have hRight : (Finset.univ : Finset (Fin 5)).filter (3 ≤ ·) = {3, 4} := by decide
    have hAbove : ((Finset.univ : Finset (Fin 5)).filter (3 < ·)).card = 1 := by decide
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, hErase, hLeft, hRight, hAbove]
    change (-1 : ℤ) • (s.residual {0, 1, 2, 4} 0 4 (-2)
      (by decide) (by decide) (by decide) (by decide) -
      _root_.SerrePositivity.DifferentialGraded.compose A (s.residual {3, 4} 3 4 0
        (by decide) (by decide) (by decide) (by decide))
        (s.hom {0, 1, 2, 3} 0 3 (-2)
          (by decide) (by decide) (by decide) (by decide)) (by decide) -
      (1 : ℤ) • _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 3 4 (by decide))
        (s.residual {0, 1, 2, 3} 0 3 (-2)
          (by decide) (by decide) (by decide) (by decide)) (by decide)) = _
    rw [hE, hR, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
    simp only [zero_sub, neg_zero, one_smul, neg_neg, neg_smul]
    have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A) (k := -3 + 1 + 1) (s.edgeHom 3 4 (by decide))
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 3) (-2 + 1))
      (s.rhs {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide))
      (by decide)
    simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] using hn
  rw [s.bianchi]
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  norm_num [Fin.sum_univ_succ]
  exact (congrArg₂ (· + ·) h₁ (congrArg₂ (· + ·) h₂ h₃)).trans
    (by simp only [zero_add])

/-- 実四次最後ホーンの K・R は、最後辺を介した微分式を満たす。 -/
lemma dgFourLastHornTopResidual_differential
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ) =
      -compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ) (by decide) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ
  have hQ : s.hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 := by
    dsimp only [s, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData]
    simp only [show ({0, 1, 2, 3} : Finset (Fin 5)) = Finset.univ.erase 4 from by decide,
      ne_eq, not_true_eq_false, ↓reduceDIte]
    split <;> rfl
  have he : ∀ I, I ≠ Finset.univ → I ≠ {0, 1, 2, 3} → s.Equation I := by
    intro I hf hm a b k hI ha hb hk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ I a b k hI ha hb hk hf
      (fun h => hm (h.trans (by decide)))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplex_rhs_top s
  rw [hQ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero] at ht
  exact (congrArg (fun f => _root_.SerrePositivity.DifferentialGraded.differential A f) ht).symm.trans
    (dgFourSimplex_rhs_top_differential s he hQ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
