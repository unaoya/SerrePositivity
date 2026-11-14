module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetArrowCompositionInputs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetNormalizationInputPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCapInputPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.RestrictedCompositionTriangleExt
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstInputTriangleEvaluation :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputTriangleEvaluation :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation (Z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetPreNormalizationInputPath_evaluation :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeFirstCompositionPath_evaluation]

lemma dgGluingHomTargetPreCapInputPath_evaluation :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreCapCompositionPath_evaluation]

lemma dgGluingHomTargetExitCollarInputPath_evaluation :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitLastCompositionPath_evaluation]

lemma dgGluingHomTargetExitCapInputPath_evaluation :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaExitCapCompositionPath_evaluation]

lemma dgGluingHomTargetArrowFirstInputLift_triangle :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowFirstInputLift R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).first := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowFirstInputLift, pullback.lift_fst,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowFirstComposition_triangle]

lemma dgGluingHomTargetArrowLastInputLift_triangle :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowLastInputLift R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).second := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowLastInputLift, pullback.lift_fst,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowLastComposition_triangle]

lemma dgGluingHomTargetFirstInputSection_triangle :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCompositionTriangle R C D E p q X Y := by
  erw [dgGluingHomTargetFirstInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection_composition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstComposition,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift_evaluation]

lemma dgGluingHomTargetLastInputSection_triangle :
    (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y := by
  erw [dgGluingHomTargetLastInputTriangleEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection_composition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastComposition,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_evaluation]

lemma dgGluingHomTargetFirstInputTriangle_hom_ext {A : SSet.{max (u + 1) v}}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
      (Δ[2] ◁ g) ≫ dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
    (hp : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputProjection R C D E p q X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputProjection R C D E p q X Y) : f = g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangle_hom_ext
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y) ht hp

lemma dgGluingHomTargetLastInputTriangle_hom_ext {A : SSet.{max (u + 1) v}}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
      (Δ[2] ◁ g) ≫ dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
    (hp : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection R C D E p q X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection R C D E p q X Y) : f = g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangle_hom_ext (Z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y) ht hp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
