module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxArrowCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：入力付き厳密模型を矢印座標と元二入力の標的へ同型で移し、指定比較を保持する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetInputCoordinateTarget : SSet.{max (u + 1) v} := by
  letI : Limits.HasLimit (cospan (dgGluingArrowCompositionEndpointPair eX eY)
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y ⊗ₘ
      dgGluingHomTargetRightIntervalInput R C D E p q X Y)) := HasLimitsOfShape.has_limit _
  exact pullback (dgGluingArrowCompositionEndpointPair eX eY)
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y ⊗ₘ
      dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetInputStrictCoordinatesIso :
    dgGluingHomTargetInputStrictPullback R C D E p q X Y ≅
      dgGluingHomTargetInputCoordinateTarget R C D E p q X Y :=
  dgGluingRestrictedDiagonalInputIso
    (compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex (p.obj X.left)) eY)
    (dgGluingFirstFixedCompositionSecond eX (Simplex.vertex (q.obj Y.right)))
    (compositionCorrespondenceDiagonal (X := dgNerve R E) (Simplex.vertex (p.obj X.left)) eY)
    (dgGluingFirstFixedCompositionDiagonal eX (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)
    (dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetInputCoordinateArrowProjection :
    dgGluingHomTargetInputCoordinateTarget R C D E p q X Y ⟶
      dgGluingArrowCompositionPullback eX eY := pullback.fst _ _

def dgGluingHomTargetInputCoordinateInputsProjection :
    dgGluingHomTargetInputCoordinateTarget R C D E p q X Y ⟶
      complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⊗
        complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) := pullback.snd _ _

def dgGluingHomTargetInputCoordinateComparison :=
  dgGluingHomTargetArrowInputStrictComparison R C D E p q X Y ≫
    (dgGluingHomTargetInputStrictCoordinatesIso R C D E p q X Y).hom

lemma dgGluingHomTargetInputCoordinateComparison_arrow :
    dgGluingHomTargetInputCoordinateComparison R C D E p q X Y ≫
      dgGluingHomTargetInputCoordinateArrowProjection R C D E p q X Y =
    dgGluingHomTargetArrowCompositionComparison R C D E p q X Y := by
  rw [dgGluingHomTargetInputCoordinateComparison,
    dgGluingHomTargetInputCoordinateArrowProjection, Category.assoc,
    dgGluingHomTargetInputStrictCoordinatesIso]
  erw [dgGluingRestrictedDiagonalInputIso_forget]
  apply pullback.hom_ext
  · rw [Category.assoc, dgGluingRestrictedDiagonalStrictForget_first]
    dsimp only [dgGluingHomTargetArrowInputStrictComparison,
      dgGluingHomTargetLastInputDiagonal, dgGluingHomTargetFirstInputDiagonal]
    simp only [Category.assoc,
      pullback.lift_snd_assoc, dgGluingHomTargetArrowFirstInputLift, pullback.lift_fst]
    all_goals rfl
  · rw [Category.assoc, dgGluingRestrictedDiagonalStrictForget_last]
    dsimp only [dgGluingHomTargetArrowInputStrictComparison,
      dgGluingHomTargetLastInputDiagonal, dgGluingHomTargetFirstInputDiagonal]
    simp only [Category.assoc,
      pullback.lift_fst_assoc, dgGluingHomTargetArrowLastInputLift, pullback.lift_fst]
    all_goals rfl

lemma dgGluingHomTargetInputCoordinateComparison_inputs :
    dgGluingHomTargetInputCoordinateComparison R C D E p q X Y ≫
      dgGluingHomTargetInputCoordinateInputsProjection R C D E p q X Y =
    lift (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y)) := by
  rw [dgGluingHomTargetInputCoordinateComparison,
    dgGluingHomTargetInputCoordinateInputsProjection, Category.assoc,
    dgGluingHomTargetInputStrictCoordinatesIso]
  erw [dgGluingRestrictedDiagonalInputIso_inputs]
  rw [dgGluingRestrictedDiagonalInputPair]
  dsimp only [dgGluingHomTargetArrowInputStrictComparison,
    dgGluingHomTargetLastInputDiagonal, dgGluingHomTargetFirstInputDiagonal]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, lift_fst, lift_snd, dgGluingHomTargetArrowInputStrictComparison,
      Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      dgGluingHomTargetArrowLastInputLift, dgGluingHomTargetArrowFirstInputLift,
      pullback.lift_snd]

lemma dgGluingHomTargetInputCoordinateComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetInputCoordinateComparison R C D E p q X Y) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff
    (dgGluingHomTargetArrowInputStrictComparison R C D E p q X Y)
    (dgGluingHomTargetInputStrictCoordinatesIso R C D E p q X Y)).mpr
    (dgGluingHomTargetArrowInputStrictComparison_equivalence R C D E p q X Y)

end SerrePositivity.InfinityCategories
