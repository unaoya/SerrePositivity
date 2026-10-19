module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanTriangleReplacementTransport
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の最上位三角形方程式

概要：A 側の微分式と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Left 候補の最上位三角形右辺は零。 -/
lemma cofiberBoundaryLeftCandidate_triangle_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).spanTwoPrefixRhs = 0 := by
  have H := SimplexData.spanInsertUnknowns_triangle_rhs_heq
    (cofiberBoundaryLeftBase f g b)
    (cofiberBoundaryLeftNative f g b hb).1.val (cofiberBoundaryLeftNative f g b hb).2.val
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (fun x y k hI hx hy hk => spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (cofiberCosliceBoundary_left_A f g b hb)
    (cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryLiftA f g b hb)
    (cofiberBoundaryRhsAB f g b hb) (mappingCone.inl (cofiberDifference f g))
    (cofiberBoundaryLeftNative f g b hb).1.property
    (cofiberBoundaryLeftNative f g b hb).2.property
    (cofiberBoundaryRhsAB_heq f g b hb).symm
    (cofiberCosliceBoundary_left_homotopy_heq f g b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(cofiberBoundaryDegree n).negOnePow := by
    rw [cofiberBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← cofiberBoundaryDegree_negOnePow n, Checks.complex_compose,
    cofiberBoundaryLiftQ_homotopy] at H
  dsimp only [cofiberBoundaryLiftA] at H
  simp only [smul_smul, neg_mul, Int.units_mul_self, Units.neg_smul, one_smul] at H
  have hz : cofiberBoundaryRhsAB f g b hb -
      (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb) +
      -(cofiberBoundaryRhsAC f g b hb) = 0 := by abel
  rw [hz] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := S)
    (cofiberCosliceBoundary_left_A f g b hb) rfl
    (show -(n : ℤ) - 2 + 1 = cofiberBoundaryDegree n by
      dsimp only [cofiberBoundaryDegree]; omega)).symm)

/-- Left 候補の最上位未知成分は零。 -/
lemma cofiberBoundaryLeftCandidate_triangle_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (Index.nonempty hI))
    (hy : y = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (cofiberBoundaryLeftCandidate f g b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
  have hq : (Finset.univ : Finset (Fin (n + 4))) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_univ, Fintype.card_fin, card_spanSuffixFaces] at hc
    omega
  have ha : (Finset.univ : Finset (Fin (n + 4))) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert 0 (spanApex_pos n)] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [cofiberBoundaryLeftCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Left 候補は最上位未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_triangle_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation Finset.univ := by
  apply SimplexData.equation_of_fixed (cofiberBoundaryLeftCandidate f g b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [cofiberBoundaryLeftCandidate_triangle_hom_zero f g b hb]
  change differential S 0 = (cofiberBoundaryLeftCandidate f g b hb).spanTwoPrefixRhs
  rw [cofiberBoundaryLeftCandidate_triangle_rhs_zero f g b hb]
  exact map_zero _

/-- Right 候補の最上位三角形右辺は零。 -/
lemma cofiberBoundaryRightCandidate_triangle_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).spanTwoPrefixRhs = 0 := by
  have H := SimplexData.spanInsertUnknowns_triangle_rhs_heq
    (cofiberBoundaryRightBase f g b)
    (cofiberBoundaryRightNative f g b hb).1.val (cofiberBoundaryRightNative f g b hb).2.val
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (fun x y k hI hx hy hk => spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (cofiberCosliceBoundary_right_A f g b hb)
    (cofiberCosliceBoundary_right_apex f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryLiftA f g b hb)
    (cofiberBoundaryRhsAC f g b hb) ((0 : Cochain A (pushoutCofiber f g) (-1)))
    (cofiberBoundaryRightNative f g b hb).1.property
    (cofiberBoundaryRightNative f g b hb).2.property
    (cofiberBoundaryRhsAC_heq f g b hb).symm
    (cofiberCosliceBoundary_right_homotopy_heq f g b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(cofiberBoundaryDegree n).negOnePow := by
    rw [cofiberBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← cofiberBoundaryDegree_negOnePow n, Checks.complex_compose,
    Cochain.zero_comp] at H
  dsimp only [cofiberBoundaryLiftA] at H
  simp only [smul_zero, sub_zero, smul_smul, neg_mul, Int.units_mul_self,
    Units.neg_smul, one_smul, add_neg_cancel] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := S)
    (cofiberCosliceBoundary_right_A f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (show -(n : ℤ) - 2 + 1 = cofiberBoundaryDegree n by
      dsimp only [cofiberBoundaryDegree]; omega)).symm)

/-- Right 候補の最上位未知成分は零。 -/
lemma cofiberBoundaryRightCandidate_triangle_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (Index.nonempty hI))
    (hy : y = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (cofiberBoundaryRightCandidate f g b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
  have hq : (Finset.univ : Finset (Fin (n + 4))) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_univ, Fintype.card_fin, card_spanSuffixFaces] at hc
    omega
  have ha : (Finset.univ : Finset (Fin (n + 4))) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert 0 (spanApex_pos n)] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  rw [cofiberBoundaryRightCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Right 候補は最上位未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_triangle_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).Equation Finset.univ := by
  apply SimplexData.equation_of_fixed (cofiberBoundaryRightCandidate f g b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [cofiberBoundaryRightCandidate_triangle_hom_zero f g b hb]
  change differential S 0 = (cofiberBoundaryRightCandidate f g b hb).spanTwoPrefixRhs
  rw [cofiberBoundaryRightCandidate_triangle_rhs_zero f g b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories
