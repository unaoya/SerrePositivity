module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeFixedTarget

/-!
概要：元の全評価の係数・始点制限を、同じ native 評価の指定定値標的へ戻す。
方針：元の共同底の可換式と unstraightening の同じ引き戻しの普遍性を使う。
規約：元の全評価の同じ制限を保持。使われ方：native 評価の実際の値写像との比較先。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 元の全評価の同じ係数・始点制限を、元の大きい共同全空間で読む。 -/
def weightedCoefficientRestrictedJointMap :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (weightedDensityTwistedJointMap F) ≫
      (smallLeftUnstraighteningIso G).hom

/-- 元の同じ全評価の制限は、元の共同底を厳密に保つ。 -/
lemma weightedCoefficientRestrictedJointMap_projection :
    weightedCoefficientRestrictedJointMap F i x ≫ leftUnstraighteningProjection G =
      weightedCoefficientNativeGlobalBase F i x := by
  rw [weightedCoefficientRestrictedJointMap, Category.assoc, Category.assoc,
    smallLeftUnstraighteningIso_projection, ← CategoryTheory.Functor.map_comp,
    weightedDensityTwistedJointMap_projection, weightedCoefficientNativeGlobalBase,
    twistedElementsReconstruction_projection]

/-- 元の全評価の同じ制限を、元の native 評価の指定定値標的へ戻す。 -/
def weightedCoefficientNativeRestrictedMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (twistedSourceElements (F.obj i).val.hom x) ⟶
      leftUnstraightening (SSet.const z :
        (SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left ⟶ SpaceInfinity.{u}) :=
  (leftUnstraighteningMap_isPullback (SSet.const z) G k
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)).lift
    (weightedCoefficientRestrictedJointMap F i x) (weightedCoefficientNativeSourceBase F i x)
    ((weightedCoefficientRestrictedJointMap_projection F i x).trans
      (weightedCoefficientNativeSourceBase_global F i x).symm)

/-- 同じ制限評価は、元の係数全空間への射影を保つ。 -/
lemma weightedCoefficientNativeRestrictedMap_projection :
    weightedCoefficientNativeRestrictedMap κ F hF i x ≫
      leftUnstraighteningProjection (SSet.const z) = weightedCoefficientNativeSourceBase F i x :=
  (leftUnstraighteningMap_isPullback (SSet.const z) G k
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)).lift_snd _ _ _

/-- 同じ制限評価を共同全空間へ戻すと、元の全評価の同じ係数・始点制限そのもの。 -/
lemma weightedCoefficientNativeRestrictedMap_map :
    weightedCoefficientNativeRestrictedMap κ F hF i x ≫ leftUnstraighteningMap (SSet.const z) G k
      (weightedCoefficientNativeEvaluationBase_target κ F hF i x) =
      weightedCoefficientRestrictedJointMap F i x :=
  (leftUnstraighteningMap_isPullback (SSet.const z) G k
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)).lift_fst _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
