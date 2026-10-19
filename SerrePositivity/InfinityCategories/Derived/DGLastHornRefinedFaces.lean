module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCanonicalFaces
public import SerrePositivity.InfinityCategories.Derived.DGTriangleRefinementComponents
public import SerrePositivity.InfinityCategories.Derived.DGTriangleFaceNormalForms

/-! # 実最後外ホーンの同じ始点細分後の三面

概要：終端面を保ち、残りの二面を同じ実閉射で細分して、全三共通辺を厳密に合わせる。
方針：回収対象族の実指定面を使い、辺の標準表示と回収 cochain の等式で比較する。
規約：辺 03 も同じ前合成になる。使われ方：新しい実最後外ホーンの組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 始点細分後の零面は元の指定終端面。 -/
def dgLastHornRefinedFace0 : Simplex A D 2 := dgLastHornCanonicalFace σ 0 (by decide)

/-- 始点細分後の一面は、元の面 023 の同じ閉射による細分。 -/
def dgLastHornRefinedFace1 : Simplex A D 2 :=
  dgSimplexSourceRefinement (dgLastHornCanonicalFace σ 1 (by decide)) q s

/-- 始点細分後の二面は、元の面 013 の同じ閉射による細分。 -/
def dgLastHornRefinedFace2 : Simplex A D 2 :=
  dgSimplexSourceRefinement (dgLastHornCanonicalFace σ 2 (by decide)) q s

/-- 共通辺 23 では、元の終端面と始点細分した面 023 が厳密に合う。 -/
lemma dgLastHornRefinedFaces_overlap01 :
    (dgNerve A D).δ 0 (dgLastHornRefinedFace0 σ) =
      (dgNerve A D).δ 0 (dgLastHornRefinedFace1 σ q s) := by
  rw [dgLastHornRefinedFace1, dgSimplexSourceRefinement_face0,
    dgTriangleFace0_normal, dgTriangleFace0_normal]
  apply congrArg (Simplex.ofEdge (pairObj ((HornData.knownData σ).obj 2)
    ((HornData.knownData σ).obj 3)))
  apply Subtype.ext
  dsimp only [Simplex.edgeCycle, dgLastHornRefinedFace0]
  exact (dgLastHornCanonicalFace_edge σ 0 (by decide) 1 2 (by decide)).trans
    (dgLastHornCanonicalFace_edge σ 1 (by decide) 1 2 (by decide)).symm

/-- 共通辺 13 でも、元の終端面と始点細分した面 013 が厳密に合う。 -/
lemma dgLastHornRefinedFaces_overlap02 :
    (dgNerve A D).δ 1 (dgLastHornRefinedFace0 σ) =
      (dgNerve A D).δ 0 (dgLastHornRefinedFace2 σ q s) := by
  rw [dgLastHornRefinedFace2, dgSimplexSourceRefinement_face0,
    dgTriangleFace1_normal, dgTriangleFace0_normal]
  apply congrArg (Simplex.ofEdge (pairObj ((HornData.knownData σ).obj 1)
    ((HornData.knownData σ).obj 3)))
  apply Subtype.ext
  dsimp only [Simplex.edgeCycle, dgLastHornRefinedFace0]
  exact (dgLastHornCanonicalFace_edge σ 0 (by decide) 0 2 (by decide)).trans
    (dgLastHornCanonicalFace_edge σ 2 (by decide) 1 2 (by decide)).symm

/-- 二つの始点細分面は、同じ辺 03 の同じ閉前合成で厳密に合う。 -/
lemma dgLastHornRefinedFaces_overlap12 :
    (dgNerve A D).δ 1 (dgLastHornRefinedFace1 σ q s) =
      (dgNerve A D).δ 1 (dgLastHornRefinedFace2 σ q s) := by
  rw [dgLastHornRefinedFace1, dgLastHornRefinedFace2,
    dgSimplexSourceRefinement_face1, dgSimplexSourceRefinement_face1]
  apply congrArg (Simplex.ofEdge (pairObj q ((HornData.knownData σ).obj 3)))
  apply Subtype.ext
  dsimp only [dgClosedCyclePrecompose, Simplex.edgeCycle]
  exact congrArg (fun f : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj 3) 0 => dgGradedPrecompose A D 0 f s)
      ((dgLastHornCanonicalFace_edge σ 1 (by decide) 0 2 (by decide)).trans
        (dgLastHornCanonicalFace_edge σ 2 (by decide) 0 2 (by decide)).symm)

end SerrePositivity.InfinityCategories
