module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryTriangleEquations
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryFirstEquation
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryLegEquations
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidateCommon

/-! # cofiber 境界の二つの充填単体

概要：全ての方程式を満たす左右の候補を dg nerve の単体へ昇格する。
方針：未知集合を四種類に分類し、各方程式と既知方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：coslice 境界の二セルの貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Left 候補は全ての部分集合で微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) : (cofiberBoundaryLeftCandidate f g b hb).Equation I := by
  by_cases hI : spanSuffixFaces n ⊆ I
  · rcases spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact cofiberBoundaryLeftCandidate_suffix_equation f g b hb
    · subst I
      exact cofiberBoundaryLeftCandidate_first_equation f g b hb
    · subst I
      exact cofiberBoundaryLeftCandidate_second_equation f g b hb
    · rw [ht, spanSuffix_insert_both]
      exact cofiberBoundaryLeftCandidate_triangle_equation f g b hb
  · exact cofiberBoundaryLeftCandidate_equation_known f g b hb I hI

/-- Left 境界の充填単体。 -/
def cofiberBoundaryLeftSimplex {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Simplex S (Complex S) (n + 3) where
  toSimplexData := cofiberBoundaryLeftCandidate f g b hb
  equation I := cofiberBoundaryLeftCandidate_equation f g b hb I

/-- Left 充填単体の既知面は元の境界に等しい。 -/
lemma cofiberBoundaryLeftSimplex_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (cofiberBoundaryLeftSimplex f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b) :=
  Simplex.ext (cofiberBoundaryLeftCandidate_pullback_face f g b hb j hj)

/-- Right 候補は全ての部分集合で微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (I : Finset (Fin (n + 4))) : (cofiberBoundaryRightCandidate f g b hb).Equation I := by
  by_cases hI : spanSuffixFaces n ⊆ I
  · rcases spanUnknown_cases I hI with hq | ha | hs | ht
    · subst I
      exact cofiberBoundaryRightCandidate_suffix_equation f g b hb
    · subst I
      exact cofiberBoundaryRightCandidate_first_equation f g b hb
    · subst I
      exact cofiberBoundaryRightCandidate_second_equation f g b hb
    · rw [ht, spanSuffix_insert_both]
      exact cofiberBoundaryRightCandidate_triangle_equation f g b hb
  · exact cofiberBoundaryRightCandidate_equation_known f g b hb I hI

/-- Right 境界の充填単体。 -/
def cofiberBoundaryRightSimplex {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Simplex S (Complex S) (n + 3) where
  toSimplexData := cofiberBoundaryRightCandidate f g b hb
  equation I := cofiberBoundaryRightCandidate_equation f g b hb I

/-- Right 充填単体の既知面は元の境界に等しい。 -/
lemma cofiberBoundaryRightSimplex_pullback_face {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (cofiberBoundaryRightSimplex f g b hb).pullback j.succAboveOrderEmb.toOrderHom =
      SSet.yonedaEquiv (spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b) :=
  Simplex.ext (cofiberBoundaryRightCandidate_pullback_face f g b hb j hj)

/-- 左右の充填単体は共通面で一致する。 -/
lemma cofiberBoundarySimplex_common {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftSimplex f g b hb).pullback (spanCommonOrderHom n) =
      (cofiberBoundaryRightSimplex f g b hb).pullback (spanCommonOrderHom n) :=
  Simplex.ext (cofiberBoundaryCandidate_common f g b hb)

end SerrePositivity.InfinityCategories
