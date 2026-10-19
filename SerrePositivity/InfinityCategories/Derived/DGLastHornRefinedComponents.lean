module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinedVertices
public import SerrePositivity.InfinityCategories.Derived.DGHornKnownFaceComponents

/-! # 閉始点細分した実ホーンの回収辺と三角 cochain

概要：新ホーンの回収成分を、元の回収成分の同じ閉射による前合成と比較する。
方針：実指定面の厳密等式から異種等号で成分を回収し、実三角形の細分公式を使う。
規約：始点を含まない成分は元のまま。使われ方：R・K の照合と Q・A の型付き輸送。
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
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 閉始点細分後の回収辺 01 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge01 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).edgeHom 0 1 (by decide))
      (dgGradedPrecompose A D 0 ((HornData.knownData σ).edgeHom 0 1 (by decide)) s) := by
  have h := dgLastHornKnownEdge_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    2 (by decide) (dgLastHornRefinedFace2 σ q s)
    (dgLastHornSourceRefinement_value2 σ q s) 0 1 (by decide)
  have h₁ := dgSimplexSourceRefinement_edge01
    (dgLastHornCanonicalFace σ 2 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj 1) 0 => dgGradedPrecompose A D 0 f s)
      (dgLastHornCanonicalFace_edge σ 2 (by decide) 0 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収辺 02 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge02 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).edgeHom 0 2 (by decide))
      (dgGradedPrecompose A D 0 ((HornData.knownData σ).edgeHom 0 2 (by decide)) s) := by
  have h := dgLastHornKnownEdge_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    1 (by decide) (dgLastHornRefinedFace1 σ q s)
    (dgLastHornSourceRefinement_value1 σ q s) 0 1 (by decide)
  have h₁ := dgSimplexSourceRefinement_edge01
    (dgLastHornCanonicalFace σ 1 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj 2) 0 => dgGradedPrecompose A D 0 f s)
      (dgLastHornCanonicalFace_edge σ 1 (by decide) 0 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収辺 12 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge12 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).edgeHom 1 2 (by decide))
      ((HornData.knownData σ).edgeHom 1 2 (by decide)) := by
  have h := dgLastHornKnownEdge_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    0 (by decide) (dgLastHornRefinedFace0 σ)
    (dgLastHornSourceRefinement_value0 σ q s) 0 1 (by decide)
  exact h.trans (heq_of_eq
    (dgLastHornCanonicalFace_edge σ 0 (by decide) 0 1 (by decide)))

/-- 閉始点細分後の回収辺 23 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge23 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).edgeHom 2 3 (by decide))
      ((HornData.knownData σ).edgeHom 2 3 (by decide)) := by
  have h := dgLastHornKnownEdge_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    0 (by decide) (dgLastHornRefinedFace0 σ)
    (dgLastHornSourceRefinement_value0 σ q s) 1 2 (by decide)
  exact h.trans (heq_of_eq
    (dgLastHornCanonicalFace_edge σ 0 (by decide) 1 2 (by decide)))

/-- 閉始点細分後の回収三角 cochain 013 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle013 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).tripleHom 0 1 3
      (by decide) (by decide))
      (dgGradedPrecompose A D (-1)
        ((HornData.knownData σ).tripleHom 0 1 3
      (by decide) (by decide)) s) := by
  have h := dgLastHornKnownTriangle_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    2 (by decide) (dgLastHornRefinedFace2 σ q s)
    (dgLastHornSourceRefinement_value2 σ q s)
  have h₁ := dgSimplexSourceRefinement_triangle
    (dgLastHornCanonicalFace σ 2 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj 3) (-1) => dgGradedPrecompose A D (-1) f s)
      (dgLastHornCanonicalFace_triangle σ 2 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収三角 cochain 023 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle023 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).tripleHom 0 2 3
      (by decide) (by decide))
      (dgGradedPrecompose A D (-1)
        ((HornData.knownData σ).tripleHom 0 2 3
      (by decide) (by decide)) s) := by
  have h := dgLastHornKnownTriangle_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    1 (by decide) (dgLastHornRefinedFace1 σ q s)
    (dgLastHornSourceRefinement_value1 σ q s)
  have h₁ := dgSimplexSourceRefinement_triangle
    (dgLastHornCanonicalFace σ 1 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj 3) (-1) => dgGradedPrecompose A D (-1) f s)
      (dgLastHornCanonicalFace_triangle σ 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収三角 cochain 123 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle123 :
    HEq ((HornData.knownData (dgLastHornSourceRefinement σ q s)).tripleHom 1 2 3
      (by decide) (by decide))
      ((HornData.knownData σ).tripleHom 1 2 3
      (by decide) (by decide)) := by
  have h := dgLastHornKnownTriangle_heq_of_face_eq (dgLastHornSourceRefinement σ q s)
    0 (by decide) (dgLastHornRefinedFace0 σ)
    (dgLastHornSourceRefinement_value0 σ q s)
  exact h.trans (heq_of_eq (dgLastHornCanonicalFace_triangle σ 0 (by decide)))

end SerrePositivity.InfinityCategories
