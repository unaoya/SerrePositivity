module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornRefinedVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHornKnownFaceComponents

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 閉始点細分後の回収辺 01 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge01 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).edgeHom 0 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 0 1 (by decide)) s) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownEdge_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value2 σ q s) 0 1 (by decide)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_edge01
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace σ 2 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 1) 0 => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 f s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_edge σ 2 (by decide) 0 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収辺 02 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge02 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).edgeHom 0 2 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 0 2 (by decide)) s) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownEdge_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    1 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value1 σ q s) 0 1 (by decide)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_edge01
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace σ 1 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) 0 => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 f s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_edge σ 1 (by decide) 0 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収辺 12 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge12 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).edgeHom 1 2 (by decide))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 1 2 (by decide)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownEdge_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    0 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value0 σ q s) 0 1 (by decide)
  exact h.trans (heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_edge σ 0 (by decide) 0 1 (by decide)))

/-- 閉始点細分後の回収辺 23 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_edge23 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).edgeHom 2 3 (by decide))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownEdge_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    0 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value0 σ q s) 1 2 (by decide)
  exact h.trans (heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_edge σ 0 (by decide) 1 2 (by decide)))

/-- 閉始点細分後の回収三角 cochain 013 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle013 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).tripleHom 0 1 3
      (by decide) (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom 0 1 3
      (by decide) (by decide)) s) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownTriangle_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    2 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value2 σ q s)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_triangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace σ 2 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-1) => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1) f s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_triangle σ 2 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収三角 cochain 023 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle023 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).tripleHom 0 2 3
      (by decide) (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom 0 2 3
      (by decide) (by decide)) s) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownTriangle_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    1 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value1 σ q s)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_triangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace σ 1 (by decide)) q s
  have h₂ := congrArg (fun f : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-1) => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1) f s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_triangle σ 1 (by decide))
  exact h.trans (heq_of_eq (h₁.trans h₂))

/-- 閉始点細分後の回収三角 cochain 123 の厳密な成分比較。 -/
lemma dgLastHornSourceRefinement_triangle123 :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)).tripleHom 1 2 3
      (by decide) (by decide))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom 1 2 3
      (by decide) (by decide)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownTriangle_heq_of_face_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement σ q s)
    0 (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_value0 σ q s)
  exact h.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_triangle σ 0 (by decide)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
