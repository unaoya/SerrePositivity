module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryTriangleEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryFirstEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryCandidateCommon

/-! # cofiber 境界の二つの充填単体

概要：全ての方程式を満たす左右の候補を dg nerve の単体へ昇格する。
方針：未知集合を四種類に分類し、各方程式と既知方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 境界の二セルの貼合せ。
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

/-- Left 候補は全ての部分集合で微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).Equation I := by
  by_cases hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I
  · rcases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_suffix_equation A D f b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_first_equation A D f b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_second_equation A D f b hb
    · rw [ht, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_both]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_triangle_equation A D f b hb
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_equation_known A D f b hb I hI

/-- Left 境界の充填単体。 -/
def dgModuleConeBoundaryLeftSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) (n + 3) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb
  equation I := dgModuleConeBoundaryLeftCandidate_equation A D f b hb I

/-- Left 充填単体の既知面は元の境界に等しい。 -/
lemma dgModuleConeBoundaryLeftSimplex_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (dgModuleConeBoundaryLeftSimplex A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_pullback_face A D f b hb j hj)

/-- Right 候補は全ての部分集合で微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).Equation I := by
  by_cases hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I
  · rcases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_suffix_equation A D f b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_first_equation A D f b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_second_equation A D f b hb
    · rw [ht, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_both]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_triangle_equation A D f b hb
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_equation_known A D f b hb I hI

/-- Right 境界の充填単体。 -/
def dgModuleConeBoundaryRightSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) (n + 3) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb
  equation I := dgModuleConeBoundaryRightCandidate_equation A D f b hb I

/-- Right 充填単体の既知面は元の境界に等しい。 -/
lemma dgModuleConeBoundaryRightSimplex_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (dgModuleConeBoundaryRightSimplex A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_pullback_face A D f b hb j hj)

/-- 左右の充填単体は共通面で一致する。 -/
lemma dgModuleConeBoundarySimplex_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftSimplex A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) =
      (dgModuleConeBoundaryRightSimplex A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryCandidate_common A D f b hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
