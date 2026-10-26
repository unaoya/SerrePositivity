module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowCompositionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationInputPaths
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapInputPaths
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedCompositionTriangleExt
/-!
概要：元入力 fiber 上の三角形評価は、指定矢印 Hom と全補正道の実三角形を回収する。
方針：二段の持ち上げの評価則を合成する。
規約：全三角形と元入力を保つ。使われ方：補正道の全端点と相対二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstInputTriangleEvaluation :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ dgGluingHomTargetFirstInputFiber R C D E p q X Y ⟶
      dgNerve R E :=
  dgGluingFirstRestrictedTriangleEvaluation
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (Simplex.vertex (q.obj Y.right)) (dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputTriangleEvaluation :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ dgGluingHomTargetLastInputFiber R C D E p q X Y ⟶
      dgNerve R E :=
  dgGluingLastRestrictedTriangleEvaluation (Z := dgNerve R E)
    (Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetPreNormalizationInputPath_evaluation :
    (Δ[2] ◁ dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetPreNormalizationInputPath, pullback.lift_fst, dgGluingPreNormalizeFirstCompositionPath_evaluation]

lemma dgGluingHomTargetPreCapInputPath_evaluation :
    (Δ[2] ◁ dgGluingHomTargetPreCapInputPath R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetPreCapInputPath, pullback.lift_fst, dgGluingIdentityCommaPreCapCompositionPath_evaluation]

lemma dgGluingHomTargetExitCollarInputPath_evaluation :
    (Δ[2] ◁ dgGluingHomTargetExitCollarInputPath R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetExitCollarInputPath, pullback.lift_fst, dgGluingExitLastCompositionPath_evaluation]

lemma dgGluingHomTargetExitCapInputPath_evaluation :
    (Δ[2] ◁ dgGluingHomTargetExitCapInputPath R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetExitCapInputPath, pullback.lift_fst, dgGluingIdentityCommaExitCapCompositionPath_evaluation]

lemma dgGluingHomTargetArrowFirstInputLift_triangle :
    (Δ[2] ◁ dgGluingHomTargetArrowFirstInputLift R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).first := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetArrowFirstInputLift, pullback.lift_fst,
    dgGluingHomTargetArrowFirstComposition_triangle]

lemma dgGluingHomTargetArrowLastInputLift_triangle :
    (Δ[2] ◁ dgGluingHomTargetArrowLastInputLift R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).second := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetArrowLastInputLift, pullback.lift_fst,
    dgGluingHomTargetArrowLastComposition_triangle]

lemma dgGluingHomTargetFirstInputSection_triangle :
    (Δ[2] ◁ dgGluingHomTargetFirstInputSection R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    dgGluingHomTargetRightCompositionTriangle R C D E p q X Y := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetFirstInputSection_composition, dgGluingHomTargetFirstComposition,
    dgGluingFirstFixedCompositionLift_evaluation]

lemma dgGluingHomTargetLastInputSection_triangle :
    (Δ[2] ◁ dgGluingHomTargetLastInputSection R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomTargetLastInputSection_composition, dgGluingHomTargetLastComposition,
    dgGluingLastFixedCompositionLift_evaluation]

lemma dgGluingHomTargetFirstInputTriangle_hom_ext {A : SSet.{max (u + 1) v}}
    {f g : A ⟶ dgGluingHomTargetFirstInputFiber R C D E p q X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
      (Δ[2] ◁ g) ≫ dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
    (hp : f ≫ dgGluingHomTargetFirstInputProjection R C D E p q X Y =
      g ≫ dgGluingHomTargetFirstInputProjection R C D E p q X Y) : f = g :=
  dgGluingFirstRestrictedTriangle_hom_ext
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (Simplex.vertex (q.obj Y.right)) (dgGluingHomTargetRightIntervalInput R C D E p q X Y) ht hp

lemma dgGluingHomTargetLastInputTriangle_hom_ext {A : SSet.{max (u + 1) v}}
    {f g : A ⟶ dgGluingHomTargetLastInputFiber R C D E p q X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
      (Δ[2] ◁ g) ≫ dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
    (hp : f ≫ dgGluingHomTargetLastInputProjection R C D E p q X Y =
      g ≫ dgGluingHomTargetLastInputProjection R C D E p q X Y) : f = g :=
  dgGluingLastRestrictedTriangle_hom_ext (Z := dgNerve R E) (Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) ht hp

end SerrePositivity.InfinityCategories
