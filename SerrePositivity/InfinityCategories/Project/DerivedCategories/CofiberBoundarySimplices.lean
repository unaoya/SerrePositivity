module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryTriangleEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryFirstEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryCandidateCommon

/-! # cofiber 境界の二つの充填単体

概要：全ての方程式を満たす左右の候補を dg nerve の単体へ昇格する。
方針：未知集合を四種類に分類し、各方程式と既知方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 境界の二セルの貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Left 候補は全ての部分集合で微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).Equation I := by
  by_cases hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I
  · rcases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_suffix_equation f g b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_first_equation f g b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_second_equation f g b hb
    · rw [ht, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_both]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_triangle_equation f g b hb
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_equation_known f g b hb I hI

/-- Left 境界の充填単体。 -/
def cofiberBoundaryLeftSimplex {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) (n + 3) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb
  equation I := cofiberBoundaryLeftCandidate_equation f g b hb I

/-- Left 充填単体の既知面は元の境界に等しい。 -/
lemma cofiberBoundaryLeftSimplex_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (cofiberBoundaryLeftSimplex f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_pullback_face f g b hb j hj)

/-- Right 候補は全ての部分集合で微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).Equation I := by
  by_cases hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I
  · rcases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_suffix_equation f g b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_first_equation f g b hb
    · subst I
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_second_equation f g b hb
    · rw [ht, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_both]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_triangle_equation f g b hb
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_equation_known f g b hb I hI

/-- Right 境界の充填単体。 -/
def cofiberBoundaryRightSimplex {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) (n + 3) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb
  equation I := cofiberBoundaryRightCandidate_equation f g b hb I

/-- Right 充填単体の既知面は元の境界に等しい。 -/
lemma cofiberBoundaryRightSimplex_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (cofiberBoundaryRightSimplex f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_pullback_face f g b hb j hj)

/-- 左右の充填単体は共通面で一致する。 -/
lemma cofiberBoundarySimplex_common {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (cofiberBoundaryLeftSimplex f g b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) =
      (cofiberBoundaryRightSimplex f g b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryCandidate_common f g b hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
