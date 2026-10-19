module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryLift
public import SerrePositivity.InfinityCategories.Derived.SpanCandidateData

/-! # 標準 cofiber 境界の明示解を挿入した候補

概要：共通の Q・A の cochain を左右の生の対象に移し、零未知データに挿入する。
方針：比較の異種等号を持つ移送と二成分置換を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填の全方程式と共通面の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Left 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque cofiberBoundaryLeftNative {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    ({q : GradedHom S ((cofiberBoundaryLeftBase f g b).obj (spanApex n))
      ((cofiberBoundaryLeftBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (cofiberBoundaryLiftQ f g b hb)}) ×
    ({a : GradedHom S ((cofiberBoundaryLeftBase f g b).obj 0)
      ((cofiberBoundaryLeftBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (cofiberBoundaryLiftA f g b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := S) (D := Complex S)
      (cofiberCosliceBoundary_left_apex f g b hb).symm rfl
      (by dsimp only [cofiberBoundaryDegree]; omega) (cofiberBoundaryLiftQ f g b hb),
    gradedHomTransportWithHEq (A := S) (D := Complex S)
      (cofiberCosliceBoundary_left_A f g b hb).symm rfl
      rfl (cofiberBoundaryLiftA f g b hb)⟩

/-- Left 側の零未知データに Q・A を挿入した候補。 -/
def cofiberBoundaryLeftCandidate {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    SimplexData S (Complex S) (n + 3) :=
  (cofiberBoundaryLeftBase f g b).spanInsertUnknowns
    (cofiberBoundaryLeftNative f g b hb).1.val (cofiberBoundaryLeftNative f g b hb).2.val

/-- Left 候補の既知の全ての方程式。 -/
lemma cofiberBoundaryLeftCandidate_equation_known {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hI : ¬ spanSuffixFaces n ⊆ I) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation I :=
  SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _ I hI)

/-- Left 候補の既知面は元の境界の制限に等しい。 -/
lemma cofiberBoundaryLeftCandidate_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (cofiberBoundaryLeftCandidate f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b)).toSimplexData := by
  rw [cofiberBoundaryLeftCandidate, SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact spanBoundaryLeftData_pullback_face (sliceUnderUncurry b) _ j hj

/-- Right 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque cofiberBoundaryRightNative {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    ({q : GradedHom S ((cofiberBoundaryRightBase f g b).obj (spanApex n))
      ((cofiberBoundaryRightBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (cofiberBoundaryLiftQ f g b hb)}) ×
    ({a : GradedHom S ((cofiberBoundaryRightBase f g b).obj 0)
      ((cofiberBoundaryRightBase f g b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (cofiberBoundaryLiftA f g b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := S) (D := Complex S)
      (cofiberCosliceBoundary_right_apex f g b hb).symm (cofiberBoundaryTarget_right_eq f g b).symm
      (by dsimp only [cofiberBoundaryDegree]; omega) (cofiberBoundaryLiftQ f g b hb),
    gradedHomTransportWithHEq (A := S) (D := Complex S)
      (cofiberCosliceBoundary_right_A f g b hb).symm (cofiberBoundaryTarget_right_eq f g b).symm
      rfl (cofiberBoundaryLiftA f g b hb)⟩

/-- Right 側の零未知データに Q・A を挿入した候補。 -/
def cofiberBoundaryRightCandidate {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    SimplexData S (Complex S) (n + 3) :=
  (cofiberBoundaryRightBase f g b).spanInsertUnknowns
    (cofiberBoundaryRightNative f g b hb).1.val (cofiberBoundaryRightNative f g b hb).2.val

/-- Right 候補の既知の全ての方程式。 -/
lemma cofiberBoundaryRightCandidate_equation_known {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) (hI : ¬ spanSuffixFaces n ⊆ I) :
    (cofiberBoundaryRightCandidate f g b hb).Equation I :=
  SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _ I hI)

/-- Right 候補の既知面は元の境界の制限に等しい。 -/
lemma cofiberBoundaryRightCandidate_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (cofiberBoundaryRightCandidate f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b)).toSimplexData := by
  rw [cofiberBoundaryRightCandidate, SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact spanBoundaryRightData_pullback_face (sliceUnderUncurry b) _ j hj

end SerrePositivity.InfinityCategories
