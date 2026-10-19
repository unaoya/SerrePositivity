module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornFaceOverlaps
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementPositiveFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence

/-! # 実四次最後ホーンの同じ閉始点細分後の指定四面

概要：終端面を保持し、残る三つの指定面を同じ実閉射で細分して六つの共有面を一致させる。
方針：零面の保存と正番号の面との可換性、元の四面の整合性を使う。
規約：同じ元の閉射を使う。使われ方：細分された実四次ホーンの構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 細分後の零面は元の指定終端面。 -/
def dgFourLastHornRefinedFace0 : Simplex A D 3 := dgFourLastHornCanonicalFace σ 0 (by decide)

/-- 細分後の一面は、元の面 0234 の同じ閉始点細分。 -/
def dgFourLastHornRefinedFace1 : Simplex A D 3 :=
  dgSimplexInitialRefinement A D (dgFourLastHornCanonicalFace σ 1 (by decide)) q s

/-- 細分後の二面は、元の面 0134 の同じ閉始点細分。 -/
def dgFourLastHornRefinedFace2 : Simplex A D 3 :=
  dgSimplexInitialRefinement A D (dgFourLastHornCanonicalFace σ 2 (by decide)) q s

/-- 細分後の三面は、元の面 0124 の同じ閉始点細分。 -/
def dgFourLastHornRefinedFace3 : Simplex A D 3 :=
  dgSimplexInitialRefinement A D (dgFourLastHornCanonicalFace σ 3 (by decide)) q s

/-- 指定終端面と細分面 0234 は共有面 234 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap01 :
    (dgNerve A D).δ 0 (dgFourLastHornRefinedFace0 σ) =
      (dgNerve A D).δ 0 (dgFourLastHornRefinedFace1 σ q s) :=
  (dgFourLastHornCanonicalFaces_overlap σ 0 1 (by decide) (by decide) (by decide)).trans
    (dgSimplexInitialRefinement_face_zero A D
      (dgFourLastHornCanonicalFace σ 1 (by decide)) q s).symm

/-- 指定終端面と細分面 0134 は共有面 134 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap02 :
    (dgNerve A D).δ 1 (dgFourLastHornRefinedFace0 σ) =
      (dgNerve A D).δ 0 (dgFourLastHornRefinedFace2 σ q s) :=
  (dgFourLastHornCanonicalFaces_overlap σ 0 2 (by decide) (by decide) (by decide)).trans
    (dgSimplexInitialRefinement_face_zero A D
      (dgFourLastHornCanonicalFace σ 2 (by decide)) q s).symm

/-- 指定終端面と細分面 0124 は共有面 124 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap03 :
    (dgNerve A D).δ 2 (dgFourLastHornRefinedFace0 σ) =
      (dgNerve A D).δ 0 (dgFourLastHornRefinedFace3 σ q s) :=
  (dgFourLastHornCanonicalFaces_overlap σ 0 3 (by decide) (by decide) (by decide)).trans
    (dgSimplexInitialRefinement_face_zero A D
      (dgFourLastHornCanonicalFace σ 3 (by decide)) q s).symm

/-- 二つの細分面 0234・0134 は共有面 034 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap12 :
    (dgNerve A D).δ 1 (dgFourLastHornRefinedFace1 σ q s) =
      (dgNerve A D).δ 1 (dgFourLastHornRefinedFace2 σ q s) := by
  have h₁ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 1 (by decide)) q s (1 : Fin 4) (by decide)
  have h₂ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 2 (by decide)) q s (1 : Fin 4) (by decide)
  apply h₁.trans
  apply Eq.trans ?_ h₂.symm
  apply dgSimplexInitialRefinement_congr
    (dgFourLastHornCanonicalFaces_overlap σ 1 2 (by decide) (by decide) (by decide)) q q
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

/-- 二つの細分面 0234・0124 は共有面 024 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap13 :
    (dgNerve A D).δ 2 (dgFourLastHornRefinedFace1 σ q s) =
      (dgNerve A D).δ 1 (dgFourLastHornRefinedFace3 σ q s) := by
  have h₁ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 1 (by decide)) q s (2 : Fin 4) (by decide)
  have h₂ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 3 (by decide)) q s (1 : Fin 4) (by decide)
  apply h₁.trans
  apply Eq.trans ?_ h₂.symm
  apply dgSimplexInitialRefinement_congr
    (dgFourLastHornCanonicalFaces_overlap σ 1 3 (by decide) (by decide) (by decide)) q q
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

/-- 二つの細分面 0134・0124 は共有面 014 で合う。 -/
lemma dgFourLastHornRefinedFaces_overlap23 :
    (dgNerve A D).δ 2 (dgFourLastHornRefinedFace2 σ q s) =
      (dgNerve A D).δ 2 (dgFourLastHornRefinedFace3 σ q s) := by
  have h₁ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 2 (by decide)) q s (2 : Fin 4) (by decide)
  have h₂ := dgSimplexInitialRefinement_face_positive A D
    (dgFourLastHornCanonicalFace σ 3 (by decide)) q s (2 : Fin 4) (by decide)
  apply h₁.trans
  apply Eq.trans ?_ h₂.symm
  apply dgSimplexInitialRefinement_congr
    (dgFourLastHornCanonicalFaces_overlap σ 2 3 (by decide) (by decide) (by decide)) q q
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories
