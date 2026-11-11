module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundaryDEquations
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTriangleReplacementTransport

/-! # 候補データの全体集合の方程式

概要：左右の候補は零に取った全体集合の三角形成分の方程式を満たす。
方針：二成分の置換後の右辺を型付きの r−u a−d に移し、明示解の式で消す。
規約：HA Proposition 1.3.1.10。使われ方：候補データの全未知方程式の最後の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：Left 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_full_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanTwoTailRhs = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b) _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase_prefixHom A D f b) _
    rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_apex A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_N A D f b hb)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTriangleD_Hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftNative A D f b hb).2.property
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN_heq_raw A D f b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_homotopy_heq A D f b hb
  · have hs (r a d : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b)
        (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)) :
        r - a - d = -d - a + r := by abel
    exact (hs _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknown_left_triangle A D f b hb).symm
  · have hne : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
      intro heq
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTriangleD_Hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := hne)]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase_unknownHom A D f b _ (Finset.subset_insert _ _) _ _ _ _ _
      _ _

/-- 概要：Left 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_full_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation Finset.univ := by
  have h0 : (Finset.univ : Finset (Fin (n + 4))) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
    intro heq
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_univ _)
  have hD : (Finset.univ : Finset (Fin (n + 4))) ≠
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro heq
    have hmem := heq ▸ (Finset.mem_univ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n))
    rcases Finset.mem_insert.mp hmem with hfirst | hprefix
    · exact ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n) hfirst
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) hprefix
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb)
    Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate_unknown_zero A D f b hb _ (Finset.subset_univ _) h0 hD]
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A 0 =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanTwoTailRhs
  rw [dgModuleFiberBoundaryLeftCandidate_full_rhs_zero]
  exact map_zero _

/-- 概要：Right 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma dgModuleFiberBoundaryRightCandidate_full_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).cospanTwoTailRhs = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b) _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase_prefixHom A D f
      b) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource_right_eq A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_apex A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_N A D f b hb)
    (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb) (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (-1))
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTriangleD_Hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightNative A D f b hb).2.property
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN_heq_raw A D f b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_homotopy_heq A D f b hb
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero]
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownN
    exact sub_self _
  · have hne : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
      intro heq
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTriangleD_Hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := hne)]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase_unknownHom A D f b _ (Finset.subset_insert _ _) _ _ _ _ _
      _ _

/-- 概要：Right 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma dgModuleFiberBoundaryRightCandidate_full_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).Equation Finset.univ := by
  have h0 : (Finset.univ : Finset (Fin (n + 4))) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
    intro heq
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_univ _)
  have hD : (Finset.univ : Finset (Fin (n + 4))) ≠
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro heq
    have hmem := heq ▸ (Finset.mem_univ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n))
    rcases Finset.mem_insert.mp hmem with hfirst | hprefix
    · exact ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n) hfirst
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) hprefix
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb)
    Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate_unknown_zero A D f b hb _ (Finset.subset_univ _) h0 hD]
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A 0 =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).cospanTwoTailRhs
  rw [dgModuleFiberBoundaryRightCandidate_full_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
