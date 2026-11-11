module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCandidateData

/-! # 標準 cofiber 境界の明示解を挿入した候補

概要：共通の Q・A の cochain を左右の生の対象に移し、零未知データに挿入する。
方針：比較の異種等号を持つ移送と二成分置換を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填の全方程式と共通面の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Left 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque cofiberBoundaryLeftNative {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    ({q : GradedHom S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb)}) ×
    ({a : GradedHom S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)}) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := S) (D := Complex S)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb).symm rfl
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := S) (D := Complex S)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb).symm rfl
      rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)⟩

/-- Left 側の零未知データに Q・A を挿入した候補。 -/
def cofiberBoundaryLeftCandidate {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData S (Complex S) (n + 3) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b).spanInsertUnknowns
    (cofiberBoundaryLeftNative f g b hb).1.val (cofiberBoundaryLeftNative f g b hb).2.val

/-- Left 候補の既知の全ての方程式。 -/
lemma cofiberBoundaryLeftCandidate_equation_known {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hI : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _ I hI)

/-- Left 候補の既知面は元の境界の制限に等しい。 -/
lemma cofiberBoundaryLeftCandidate_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (cofiberBoundaryLeftCandidate f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).toSimplexData := by
  rw [cofiberBoundaryLeftCandidate, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_pullback_face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _ j hj

/-- Right 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque cofiberBoundaryRightNative {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    ({q : GradedHom S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb)}) ×
    ({a : GradedHom S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)}) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := S) (D := Complex S)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b).symm
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := S) (D := Complex S)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b).symm
      rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)⟩

/-- Right 側の零未知データに Q・A を挿入した候補。 -/
def cofiberBoundaryRightCandidate {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData S (Complex S) (n + 3) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).spanInsertUnknowns
    (cofiberBoundaryRightNative f g b hb).1.val (cofiberBoundaryRightNative f g b hb).2.val

/-- Right 候補の既知の全ての方程式。 -/
lemma cofiberBoundaryRightCandidate_equation_known {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hI : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) :
    (cofiberBoundaryRightCandidate f g b hb).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _ I hI)

/-- Right 候補の既知面は元の境界の制限に等しい。 -/
lemma cofiberBoundaryRightCandidate_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (cofiberBoundaryRightCandidate f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).toSimplexData := by
  rw [cofiberBoundaryRightCandidate, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_pullback_face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) _ j hj

end SerrePositivity.InfinityCategories.Project.DerivedCategories
