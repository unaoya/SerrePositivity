module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryLiftData
public import SerrePositivity.InfinityCategories.Derived.SpanCandidateData

/-! # 標準 cofiber 境界の明示解を挿入した候補

概要：共通の Q・A の cochain を左右の生の対象に移し、零未知データに挿入する。
方針：比較の異種等号を持つ移送と二成分置換を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填の全方程式と共通面の検証。
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

/-- Left 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque dgModuleConeBoundaryLeftNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    ({q : GradedHom A ((dgModuleConeBoundaryLeftBase A D f b).obj (spanApex n))
      ((dgModuleConeBoundaryLeftBase A D f b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (dgModuleConeBoundaryLiftQ A D f b hb)}) ×
    ({a : GradedHom A ((dgModuleConeBoundaryLeftBase A D f b).obj 0)
      ((dgModuleConeBoundaryLeftBase A D f b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (dgModuleConeBoundaryLiftA A D f b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (dgModuleConeBoundary_left_apex A D f b hb).symm rfl
      (by dsimp only [dgModuleConeBoundaryDegree]; omega) (dgModuleConeBoundaryLiftQ A D f b hb),
    gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (dgModuleConeBoundary_left_A A D f b hb).symm rfl
      rfl (dgModuleConeBoundaryLiftA A D f b hb)⟩

/-- Left 側の零未知データに Q・A を挿入した候補。 -/
def dgModuleConeBoundaryLeftCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    SimplexData A (RightModule A D) (n + 3) :=
  (dgModuleConeBoundaryLeftBase A D f b).spanInsertUnknowns
    (dgModuleConeBoundaryLeftNative A D f b hb).1.val (dgModuleConeBoundaryLeftNative A D f b
      hb).2.val

/-- Left 候補の既知の全ての方程式。 -/
lemma dgModuleConeBoundaryLeftCandidate_equation_known {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hI : ¬ spanSuffixFaces n ⊆ I) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation I :=
  SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _ I hI)

/-- Left 候補の既知面は元の境界の制限に等しい。 -/
lemma dgModuleConeBoundaryLeftCandidate_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b)).toSimplexData := by
  rw [dgModuleConeBoundaryLeftCandidate, SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact spanBoundaryLeftData_pullback_face (sliceUnderUncurry b) _ j hj

/-- Right 側の生の端点・次数に移した Q・A と共通解との比較。 -/
opaque dgModuleConeBoundaryRightNative {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    ({q : GradedHom A ((dgModuleConeBoundaryRightBase A D f b).obj (spanApex n))
      ((dgModuleConeBoundaryRightBase A D f b).obj (Fin.last (n + 3))) (-(n : ℤ)) //
      HEq q (dgModuleConeBoundaryLiftQ A D f b hb)}) ×
    ({a : GradedHom A ((dgModuleConeBoundaryRightBase A D f b).obj 0)
      ((dgModuleConeBoundaryRightBase A D f b).obj (Fin.last (n + 3))) (-(n : ℤ) - 1) //
      HEq a (dgModuleConeBoundaryLiftA A D f b hb)}) :=
  ⟨gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (dgModuleConeBoundary_right_apex A D f b hb).symm (dgModuleConeBoundaryTarget_right_eq A
        D f b).symm
      (by dsimp only [dgModuleConeBoundaryDegree]; omega) (dgModuleConeBoundaryLiftQ A D f b hb),
    gradedHomTransportWithHEq (A := A) (D := RightModule A D)
      (dgModuleConeBoundary_right_A A D f b hb).symm (dgModuleConeBoundaryTarget_right_eq A D f
        b).symm
      rfl (dgModuleConeBoundaryLiftA A D f b hb)⟩

/-- Right 側の零未知データに Q・A を挿入した候補。 -/
def dgModuleConeBoundaryRightCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    SimplexData A (RightModule A D) (n + 3) :=
  (dgModuleConeBoundaryRightBase A D f b).spanInsertUnknowns
    (dgModuleConeBoundaryRightNative A D f b hb).1.val (dgModuleConeBoundaryRightNative A D f b
      hb).2.val

/-- Right 候補の既知の全ての方程式。 -/
lemma dgModuleConeBoundaryRightCandidate_equation_known {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) (hI : ¬ spanSuffixFaces n ⊆ I) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).Equation I :=
  SimplexData.spanInsertUnknowns_equation _ _ _ I hI
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _ I hI)

/-- Right 候補の既知面は元の境界の制限に等しい。 -/
lemma dgModuleConeBoundaryRightCandidate_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b)).toSimplexData := by
  rw [dgModuleConeBoundaryRightCandidate, SimplexData.spanInsertUnknowns_pullback_face _ _ _ j hj]
  exact spanBoundaryRightData_pullback_face (sliceUnderUncurry b) _ j hj

end SerrePositivity.InfinityCategories
