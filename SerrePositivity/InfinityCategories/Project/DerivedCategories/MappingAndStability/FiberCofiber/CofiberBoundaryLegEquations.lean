module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の B・C 側方程式

概要：脚側の零未知成分と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- A は二番目の固定頂点と後続部分の集合に属さない。 -/
lemma spanFirst_notMem_secondSuffix (n : ℕ) :
    (0 : Fin (n + 4)) ∉ insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanPrefix_notMem_suffix 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)⟩

/-- A を含む挿入集合は二番目の固定頂点側の集合に含まれない。 -/
lemma spanFirst_insert_not_subset_second (n : ℕ) :
    ¬ insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ⊆
      insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
  intro h
  exact spanFirst_notMem_secondSuffix n (h (Finset.mem_insert_self _ _))

/-- Left 候補の脚側未知集合の右辺は零。 -/
lemma cofiberBoundaryLeftCandidate_second_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_B f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_inclusion_heq f g b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ_inclusionB,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_B f g b hb) rfl
    (show -(n : ℤ) - 1 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 from rfl)).symm)

/-- Left 候補の脚側未知集合の成分は零。 -/
lemma cofiberBoundaryLeftCandidate_second_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Left 候補は脚側未知集合の方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_second_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [cofiberBoundaryLeftCandidate_second_hom_zero f g b hb]
  change differential S 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).spanOnePrefixRhs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  rw [cofiberBoundaryLeftCandidate_second_rhs_zero f g b hb]
  exact map_zero _

/-- Right 候補の脚側未知集合の右辺は零。 -/
lemma cofiberBoundaryRightCandidate_second_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_C f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_inclusion_heq f g b hb)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ_inclusionC,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_C f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (show -(n : ℤ) - 1 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 from rfl)).symm)

/-- Right 候補の脚側未知集合の成分は零。 -/
lemma cofiberBoundaryRightCandidate_second_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Right 候補は脚側未知集合の方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_second_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [cofiberBoundaryRightCandidate_second_hom_zero f g b hb]
  change differential S 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).spanOnePrefixRhs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)
  rw [cofiberBoundaryRightCandidate_second_rhs_zero f g b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
