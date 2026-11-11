module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の B・C 側方程式

概要：脚側の零未知成分と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- Left 候補の脚側未知集合の右辺は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanFirst_insert_not_subset_second n)]
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftBase A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftNative A D f b hb).1.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_B A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_apex A D f b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftNative A D f b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB_heq A D f b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_inclusion_heq A D f b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftQ_inr,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_B A D f b hb) rfl
    (show -(n : ℤ) - 1 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 from rfl)).symm)

/-- Left 候補の脚側未知集合の成分は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).hom
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Left 候補は脚側未知集合の方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [dgModuleConeBoundaryLeftCandidate_second_hom_zero A D f b hb]
  change differential A 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).spanOnePrefixRhs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  rw [dgModuleConeBoundaryLeftCandidate_second_rhs_zero A D f b hb]
  exact map_zero _

/-- Right 候補の脚側未知集合の右辺は零。 -/
lemma dgModuleConeBoundaryRightCandidate_second_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanFirst_insert_not_subset_second n)]
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightNative A D f b hb).1.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_C A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_apex A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC A D f b hb)
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.zeroModule A D)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightNative A D f b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC_heq A D f b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_inclusion_heq A D f b hb)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsC_eq_zero] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_C A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget_right_eq A D f b)
    (show -(n : ℤ) - 1 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 from rfl)).symm)

/-- Right 候補の脚側未知集合の成分は零。 -/
lemma dgModuleConeBoundaryRightCandidate_second_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).hom
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Right 候補は脚側未知集合の方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_second_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [dgModuleConeBoundaryRightCandidate_second_hom_zero A D f b hb]
  change differential A 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).spanOnePrefixRhs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  rw [dgModuleConeBoundaryRightCandidate_second_rhs_zero A D f b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
