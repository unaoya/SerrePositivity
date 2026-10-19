module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の B・C 側方程式

概要：脚側の零未知成分と後続置換の右辺変化を接続する。
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

/-- Left 候補の脚側未知集合の右辺は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n) = 0 := by
  unfold dgModuleConeBoundaryLeftCandidate SimplexData.spanInsertUnknowns
    SimplexData.spanOnePrefixRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (dgModuleConeBoundaryLeftBase A D f b) (dgModuleConeBoundaryLeftNative A D f b hb).1.val
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (dgModuleConeBoundary_left_B A D f b hb)
    (dgModuleConeBoundary_left_apex A D f b hb) rfl
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhsB A D f b hb)
    (moduleConeInrElement A D f)
    (dgModuleConeBoundaryLeftNative A D f b hb).1.property
    (dgModuleConeBoundaryRhsB_heq A D f b hb).symm
    (dgModuleConeBoundary_left_inclusion_heq A D f b hb)
  rw [dgModuleConeBoundaryLiftQ_inr,
    ← dgModuleConeBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := A)
    (dgModuleConeBoundary_left_B A D f b hb) rfl
    (show -(n : ℤ) - 1 + 1 = dgModuleConeBoundaryDegree n + 1 from rfl)).symm)

/-- Left 候補の脚側未知集合の成分は零。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (spanSecondPrefix n) (spanSuffixFaces n)).card)
    (hx : x = (insert (spanSecondPrefix n) (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert (spanSecondPrefix n) (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).hom
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n), card_spanSuffixFaces] at hc
    omega
  have ha : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [dgModuleConeBoundaryLeftCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Left 候補は脚側未知集合の方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_second_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed (dgModuleConeBoundaryLeftCandidate A D f b hb)
    (insert (spanSecondPrefix n) (spanSuffixFaces n)) (spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
    (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [dgModuleConeBoundaryLeftCandidate_second_hom_zero A D f b hb]
  change differential A 0 = (dgModuleConeBoundaryLeftCandidate A D f b hb).spanOnePrefixRhs
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
  rw [dgModuleConeBoundaryLeftCandidate_second_rhs_zero A D f b hb]
  exact map_zero _

/-- Right 候補の脚側未知集合の右辺は零。 -/
lemma dgModuleConeBoundaryRightCandidate_second_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n) = 0 := by
  unfold dgModuleConeBoundaryRightCandidate SimplexData.spanInsertUnknowns
    SimplexData.spanOnePrefixRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (dgModuleConeBoundaryRightBase A D f b) (dgModuleConeBoundaryRightNative A D f b hb).1.val
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (dgModuleConeBoundary_right_C A D f b hb)
    (dgModuleConeBoundary_right_apex A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhsC A D f b hb)
    (0 : GradedHom A (zeroModule A D)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) 0)
    (dgModuleConeBoundaryRightNative A D f b hb).1.property
    (dgModuleConeBoundaryRhsC_heq A D f b hb).symm
    (dgModuleConeBoundary_right_inclusion_heq A D f b hb)
  simp only [compose_zero, smul_zero, sub_zero, dgModuleConeBoundaryRhsC_eq_zero] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := A)
    (dgModuleConeBoundary_right_C A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
    (show -(n : ℤ) - 1 + 1 = dgModuleConeBoundaryDegree n + 1 from rfl)).symm)

/-- Right 候補の脚側未知集合の成分は零。 -/
lemma dgModuleConeBoundaryRightCandidate_second_hom_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (spanSecondPrefix n) (spanSuffixFaces n)).card)
    (hx : x = (insert (spanSecondPrefix n) (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert (spanSecondPrefix n) (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).hom
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n), card_spanSuffixFaces] at hc
    omega
  have ha : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [dgModuleConeBoundaryRightCandidate_hom_of_ne A D f b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Right 候補は脚側未知集合の方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_second_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).Equation
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed (dgModuleConeBoundaryRightCandidate A D f b hb)
    (insert (spanSecondPrefix n) (spanSuffixFaces n)) (spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
    (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [dgModuleConeBoundaryRightCandidate_second_hom_zero A D f b hb]
  change differential A 0 = (dgModuleConeBoundaryRightCandidate A D f b hb).spanOnePrefixRhs
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
  rw [dgModuleConeBoundaryRightCandidate_second_rhs_zero A D f b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories
