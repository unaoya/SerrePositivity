module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeHomotopy
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluationImage
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.HomotopyTransformationRestriction

/-!
概要：共同密度変換の同じ係数・始点制限は、元の native 評価変換の指定頂点に一致する。
方針：元の native 評価の両端を厳密に回収し、同じ全円柱の制限公式を使う。
規約：元の図式・頂点を保持。使われ方：native 評価余錐の実際の unstraightening の像。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 共同 Hom の同じ制限を、元の native 評価図式に厳密に正規化する。 -/
lemma weightedCoefficientNativeEvaluationBase_source : k ≫ H = D :=
  (weightedCoefficientEvaluationBase_source F i x).trans
    (weightedCoefficientNativeEvaluationDiagram_eq κ F i x).symm

/-- 共同分類の同じ制限を、元の native 評価頂点に厳密に正規化する。 -/
lemma weightedCoefficientNativeEvaluationBase_target : k ≫ G = SSet.const z :=
  (weightedCoefficientEvaluationBase_target F i x).trans
    (congrArg SSet.const (weightedCoefficientNativeEvaluationVertex_eq κ F hF i x).symm)

/-- 元の native 評価の両端を保持した、共同変換空間の実際の制限射。 -/
def weightedCoefficientNativeJointRestriction :=
  normalizedLeftTransformationRestriction H G k D (SSet.const z)
    (weightedCoefficientNativeEvaluationBase_source κ F i x)
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)

/-- c1 の元の指定変換頂点を制限すると、同じ native 評価変換の指定頂点そのもの。 -/
lemma weightedCoefficientNativeJointRestriction_vertex :
    (weightedCoefficientNativeJointRestriction κ F hF i x).app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (weightedDensityTransformation F).realization.transformation)) =
      weightedCoefficientNativeEvaluatedTransformation κ F hF i x := by
  have ht : homotopyTransformationVertex (weightedDensityJointHomotopy F) =
      (smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (weightedDensityTransformation F).realization.transformation) :=
    homotopyTransformationVertex_recovered _
  rw [← ht]
  exact (homotopyTransformationVertex_restriction (weightedDensityJointHomotopy F) k
    (weightedCoefficientNativeEvaluationBase_source κ F i x)
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)
    (weightedCoefficientNativeEvaluationHomotopy κ F hF i x)
    (weightedCoefficientNativeEvaluationHomotopy_h κ F hF i x)).trans
      (weightedCoefficientNativeEvaluatedTransformation_eq κ F hF i x).symm

end SerrePositivity.InfinityCategories.F2.Ind
