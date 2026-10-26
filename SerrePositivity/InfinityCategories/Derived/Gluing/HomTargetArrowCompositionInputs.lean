module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCollarTriangleEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedCompositionTriangleExt
/-!
概要：指定元矢印 Hom の二合成対応を、元左右 Hom 入力付き fiber へ持ち上げる。
方針：全三角形とその可変辺を回収し、元鎖射影とともに引き戻しへ入れる。
規約：指定比較の実作用を変えない。使われ方：実 lax Hom 比較の逆・往復則への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => Edge.ofTruncated (X := dgNerve R E)
  (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X))
local notation "eY" => Edge.ofTruncated (X := dgNerve R E)
  (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetArrowFirstComposition :
    P ⟶ dgGluingFirstFixedCompositionSpace eX (Simplex.vertex (q.obj Y.right)) :=
  dgGluingHomTargetArrowCompositionComparison R C D E p q X Y ≫ pullback.fst _ _

def dgGluingHomTargetArrowLastComposition :
    P ⟶ compositionCorrespondence (X := dgNerve R E) (Simplex.vertex (p.obj X.left)) eY :=
  dgGluingHomTargetArrowCompositionComparison R C D E p q X Y ≫ pullback.snd _ _

lemma dgGluingHomTargetArrowFirstComposition_triangle :
    (Δ[2] ◁ dgGluingHomTargetArrowFirstComposition R C D E p q X Y) ≫
      dgGluingFirstFixedCompositionEvaluation eX (Simplex.vertex (q.obj Y.right)) =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).first := by
  erw [dgGluingHomTargetArrowFirstComposition, dgGluingHomTargetArrowCompositionComparison,
    Category.assoc, dgGluingArrowCompositionIso_inv_first,
    dgGluingArrowHomFirstComposition, dgGluingFirstFixedCompositionLift_evaluation]
  rfl

lemma dgGluingHomTargetArrowLastComposition_triangle :
    (Δ[2] ◁ dgGluingHomTargetArrowLastComposition R C D E p q X Y) ≫
      compositionCorrespondenceEvaluation (X := dgNerve R E) (Simplex.vertex (p.obj X.left)) eY =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).second := by
  erw [dgGluingHomTargetArrowLastComposition, dgGluingHomTargetArrowCompositionComparison,
    Category.assoc, dgGluingArrowCompositionIso_inv_last,
    dgGluingArrowHomLastComposition, dgGluingLastFixedCompositionLift_evaluation]
  rfl

lemma dgGluingHomTargetArrowFirstComposition_input :
    dgGluingHomTargetArrowFirstComposition R C D E p q X Y ≫
      dgGluingFirstFixedCompositionSecond eX (Simplex.vertex (q.obj Y.right)) =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
      dgGluingHomTargetRightIntervalInput R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [dgGluingFirstFixedCompositionSecond_uncurry, uncurry_natural_left]
  change (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
    ((Δ[2] ◁ dgGluingHomTargetArrowFirstComposition R C D E p q X Y) ≫
      dgGluingFirstFixedCompositionEvaluation eX (Simplex.vertex (q.obj Y.right))) = _
  rw [dgGluingHomTargetArrowFirstComposition_triangle,
    dgGluingHomTargetArrowTriangles_first_variable]

lemma dgGluingHomTargetArrowLastComposition_input :
    dgGluingHomTargetArrowLastComposition R C D E p q X Y ≫
      compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex (p.obj X.left)) eY =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
      dgGluingHomTargetLeftIntervalInput R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [compositionCorrespondenceFirst_uncurry, uncurry_natural_left]
  change (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
    ((Δ[2] ◁ dgGluingHomTargetArrowLastComposition R C D E p q X Y) ≫
      compositionCorrespondenceEvaluation (X := dgNerve R E)
        (Simplex.vertex (p.obj X.left)) eY) = _
  rw [dgGluingHomTargetArrowLastComposition_triangle,
    dgGluingHomTargetArrowTriangles_second_variable]

def dgGluingHomTargetArrowFirstInputLift :
    P ⟶ dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetArrowFirstComposition R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y))
    (dgGluingHomTargetArrowFirstComposition_input R C D E p q X Y)

def dgGluingHomTargetArrowLastInputLift :
    P ⟶ dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetArrowLastComposition R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
    (dgGluingHomTargetArrowLastComposition_input R C D E p q X Y)

lemma dgGluingHomTargetArrowFirstInputLift_input :
    dgGluingHomTargetArrowFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetArrowLastInputLift_input :
    dgGluingHomTargetArrowLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
