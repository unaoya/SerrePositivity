module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanTriangleReplacementTransport
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の最上位三角形方程式

概要：Q・A の挿入による三角形右辺の変化を合成し、最上位の零成分の方程式を証明する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- Left 候補の最上位三角形右辺は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_triangle_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).spanTwoPrefixRhs = 0 := by
  have H := SimplexData.spanInsertUnknowns_triangle_rhs_heq
    (dgModuleConeBoundaryLeftBase A D f b)
    (dgModuleConeBoundaryLeftNative A D f b hb).1.val (dgModuleConeBoundaryLeftNative A D f b
      hb).2.val
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (fun x y k hI hx hy hk => spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (dgModuleConeBoundary_left_A A D f b hb)
    (dgModuleConeBoundary_left_apex A D f b hb) rfl
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryLiftA A D f b hb)
    (dgModuleConeBoundaryRhsAB A D f b hb) (moduleConeInlElement A D f)
    (dgModuleConeBoundaryLeftNative A D f b hb).1.property
    (dgModuleConeBoundaryLeftNative A D f b hb).2.property
    (dgModuleConeBoundaryRhsAB_heq A D f b hb).symm
    (dgModuleConeBoundary_left_homotopy_heq A D f b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(dgModuleConeBoundaryDegree n).negOnePow := by
    rw [dgModuleConeBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← dgModuleConeBoundaryDegree_negOnePow n, dgModuleConeBoundaryLiftQ_inl] at H
  dsimp only [dgModuleConeBoundaryLiftA] at H
  simp only [smul_smul, neg_mul, Int.units_mul_self, Units.neg_smul, one_smul] at H
  have hz : dgModuleConeBoundaryRhsAB A D f b hb -
      (dgModuleConeBoundaryRhsAB A D f b hb - dgModuleConeBoundaryRhsAC A D f b hb) +
      -(dgModuleConeBoundaryRhsAC A D f b hb) = 0 := by abel
  rw [hz] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := A)
    (dgModuleConeBoundary_left_A A D f b hb) rfl
    (show -(n : ℤ) - 2 + 1 = dgModuleConeBoundaryDegree n by
      dsimp only [dgModuleConeBoundaryDegree]; omega)).symm)

/-- Left 候補の最上位未知成分は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_triangle_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (Index.nonempty hI))
    (hy : y = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
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
  rw [dgModuleConeBoundaryLeftCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Left 候補は最上位未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_triangle_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation Finset.univ := by
  apply SimplexData.equation_of_fixed (dgModuleConeBoundaryLeftCandidate A D f b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [dgModuleConeBoundaryLeftCandidate_triangle_hom_zero A D f b hb]
  change differential A 0 = (dgModuleConeBoundaryLeftCandidate A D f b hb).spanTwoPrefixRhs
  rw [dgModuleConeBoundaryLeftCandidate_triangle_rhs_zero A D f b hb]
  exact map_zero _

/-- Right 候補の最上位三角形右辺は零。 -/
lemma dgModuleConeBoundaryRightCandidate_triangle_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).spanTwoPrefixRhs = 0 := by
  have H := SimplexData.spanInsertUnknowns_triangle_rhs_heq
    (dgModuleConeBoundaryRightBase A D f b)
    (dgModuleConeBoundaryRightNative A D f b hb).1.val (dgModuleConeBoundaryRightNative A D f b
      hb).2.val
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (fun x y k hI hx hy hk => spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b)
      _ (Finset.subset_insert _ _) x y k hI hx hy hk)
    (dgModuleConeBoundary_right_A A D f b hb)
    (dgModuleConeBoundary_right_apex A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryLiftA A D f b hb)
    (dgModuleConeBoundaryRhsAC A D f b hb) ((0 : GradedHom A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)))
    (dgModuleConeBoundaryRightNative A D f b hb).1.property
    (dgModuleConeBoundaryRightNative A D f b hb).2.property
    (dgModuleConeBoundaryRhsAC_heq A D f b hb).symm
    (dgModuleConeBoundary_right_homotopy_heq A D f b hb)
  have hsign : ((n : ℤ) + 2).negOnePow = -(dgModuleConeBoundaryDegree n).negOnePow := by
    rw [dgModuleConeBoundaryDegree_negOnePow]
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [hsign, ← dgModuleConeBoundaryDegree_negOnePow n, compose_zero] at H
  dsimp only [dgModuleConeBoundaryLiftA] at H
  simp only [smul_zero, sub_zero, smul_smul, neg_mul, Int.units_mul_self,
    Units.neg_smul, one_smul, add_neg_cancel] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := A)
    (dgModuleConeBoundary_right_A A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (show -(n : ℤ) - 2 + 1 = dgModuleConeBoundaryDegree n by
      dsimp only [dgModuleConeBoundaryDegree]; omega)).symm)

/-- Right 候補の最上位未知成分は零。 -/
lemma dgModuleConeBoundaryRightCandidate_triangle_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (hx : x = Finset.univ.min' (Index.nonempty hI))
    (hy : y = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).hom Finset.univ x y k hI hx hy hk = 0 := by
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
  rw [dgModuleConeBoundaryRightCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_univ _) x y k hI hx hy hk

/-- Right 候補は最上位未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_triangle_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).Equation Finset.univ := by
  apply SimplexData.equation_of_fixed (dgModuleConeBoundaryRightCandidate A D f b hb)
    Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp) (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [dgModuleConeBoundaryRightCandidate_triangle_hom_zero A D f b hb]
  change differential A 0 = (dgModuleConeBoundaryRightCandidate A D f b hb).spanTwoPrefixRhs
  rw [dgModuleConeBoundaryRightCandidate_triangle_rhs_zero A D f b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories
