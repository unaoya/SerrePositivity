module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTriangleReplacementTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の最上位三角形方程式

概要：Q・A の挿入による三角形右辺の変化を合成し、最上位の零成分の方程式を証明する。
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

/-- Left 候補の最上位三角形右辺は零。 -/
lemma cofiberBoundaryLeftCandidate_triangle_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).spanTwoPrefixRhs = 0 := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanInsertUnknowns_triangle_rhs_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).2.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (fun x y k hI hx hy hk => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb) (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).2.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_homotopy_heq f g b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ_homotopy] at H
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA] at H
  simp only [smul_smul, neg_mul, Int.units_mul_self, Units.neg_smul, one_smul] at H
  have hz : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb -
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) +
      -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) = 0 := by abel
  rw [hz] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb) rfl
    (show -(n : ℤ) - 2 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)).symm)

/-- Left 候補の最上位未知成分は零。 -/
lemma cofiberBoundaryLeftCandidate_triangle_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
  have hq : (Finset.univ : Finset (Fin (n + 4))) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_univ, Fintype.card_fin, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : (Finset.univ : Finset (Fin (n + 4))) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Left 候補は最上位未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_triangle_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).Equation Finset.univ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [cofiberBoundaryLeftCandidate_triangle_hom_zero f g b hb]
  change differential S 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).spanTwoPrefixRhs
  rw [cofiberBoundaryLeftCandidate_triangle_rhs_zero f g b hb]
  exact map_zero _

/-- Right 候補の最上位三角形右辺は零。 -/
lemma cofiberBoundaryRightCandidate_triangle_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).spanTwoPrefixRhs = 0 := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanInsertUnknowns_triangle_rhs_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).2.val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
    (fun x y k hI hx hy hk => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) ((0 : Cochain A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).2.property
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC_heq f g b hb).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_homotopy_heq f g b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose,
    Cochain.zero_comp] at H
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA] at H
  simp only [smul_zero, sub_zero, smul_smul, neg_mul, Int.units_mul_self,
    Units.neg_smul, one_smul, add_neg_cancel] at H
  exact eq_of_heq (H.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
    (show -(n : ℤ) - 2 + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)).symm)

/-- Right 候補の最上位未知成分は零。 -/
lemma cofiberBoundaryRightCandidate_triangle_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
  have hq : (Finset.univ : Finset (Fin (n + 4))) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_univ, Fintype.card_fin, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
    omega
  have ha : (Finset.univ : Finset (Fin (n + 4))) ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    have hc := congrArg Finset.card h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Right 候補は最上位未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_triangle_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).Equation Finset.univ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [cofiberBoundaryRightCandidate_triangle_hom_zero f g b hb]
  change differential S 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).spanTwoPrefixRhs
  rw [cofiberBoundaryRightCandidate_triangle_rhs_zero f g b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
