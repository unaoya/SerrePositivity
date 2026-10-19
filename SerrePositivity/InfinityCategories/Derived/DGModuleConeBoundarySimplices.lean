module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryTriangleEquations
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryFirstEquation
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidateCommon

/-! # cofiber 境界の二つの充填単体

概要：全ての方程式を満たす左右の候補を dg nerve の単体へ昇格する。
方針：未知集合を四種類に分類し、各方程式と既知方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 境界の二セルの貼合せ。
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

/-- Left 候補は全ての部分集合で微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) : (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation I := by
  by_cases hI : spanSuffixFaces n ⊆ I
  · rcases spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact dgModuleConeBoundaryLeftCandidate_suffix_equation A D f b hb
    · subst I
      exact dgModuleConeBoundaryLeftCandidate_first_equation A D f b hb
    · subst I
      exact dgModuleConeBoundaryLeftCandidate_second_equation A D f b hb
    · rw [ht, spanSuffix_insert_both]
      exact dgModuleConeBoundaryLeftCandidate_triangle_equation A D f b hb
  · exact dgModuleConeBoundaryLeftCandidate_equation_known A D f b hb I hI

/-- Left 境界の充填単体。 -/
def dgModuleConeBoundaryLeftSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    Simplex A (RightModule A D) (n + 3) where
  toSimplexData := dgModuleConeBoundaryLeftCandidate A D f b hb
  equation I := dgModuleConeBoundaryLeftCandidate_equation A D f b hb I

/-- Left 充填単体の既知面は元の境界に等しい。 -/
lemma dgModuleConeBoundaryLeftSimplex_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (dgModuleConeBoundaryLeftSimplex A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b) :=
  Simplex.ext (dgModuleConeBoundaryLeftCandidate_pullback_face A D f b hb j hj)

/-- Right 候補は全ての部分集合で微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (I : Finset (Fin (n + 4))) : (dgModuleConeBoundaryRightCandidate A D f b hb).Equation I := by
  by_cases hI : spanSuffixFaces n ⊆ I
  · rcases spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact dgModuleConeBoundaryRightCandidate_suffix_equation A D f b hb
    · subst I
      exact dgModuleConeBoundaryRightCandidate_first_equation A D f b hb
    · subst I
      exact dgModuleConeBoundaryRightCandidate_second_equation A D f b hb
    · rw [ht, spanSuffix_insert_both]
      exact dgModuleConeBoundaryRightCandidate_triangle_equation A D f b hb
  · exact dgModuleConeBoundaryRightCandidate_equation_known A D f b hb I hI

/-- Right 境界の充填単体。 -/
def dgModuleConeBoundaryRightSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    Simplex A (RightModule A D) (n + 3) where
  toSimplexData := dgModuleConeBoundaryRightCandidate A D f b hb
  equation I := dgModuleConeBoundaryRightCandidate_equation A D f b hb I

/-- Right 充填単体の既知面は元の境界に等しい。 -/
lemma dgModuleConeBoundaryRightSimplex_pullback_face {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (dgModuleConeBoundaryRightSimplex A D f b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b) :=
  Simplex.ext (dgModuleConeBoundaryRightCandidate_pullback_face A D f b hb j hj)

/-- 左右の充填単体は共通面で一致する。 -/
lemma dgModuleConeBoundarySimplex_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftSimplex A D f b hb).pullback (spanCommonOrderHom n) =
      (dgModuleConeBoundaryRightSimplex A D f b hb).pullback (spanCommonOrderHom n) :=
  Simplex.ext (dgModuleConeBoundaryCandidate_common A D f b hb)

end SerrePositivity.InfinityCategories
