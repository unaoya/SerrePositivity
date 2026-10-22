module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityRestrictedTransformation
public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyTransformationRestriction

/-!
概要：共同 Hom の元の変換空間から評価密度変換への実際の制限射を与える。
方針：元の底の包含への前合成を区間模型に作用させ、証明済みの両端等式で正規化する。
規約：c1 で実現した元の変換頂点における作用を厳密に照合する。
使われ方：写像空間比較の底変換自然性を同じ密度評価へ適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F

/-- 元の共同 Hom の変換空間への、同じ始点固定包含による制限。 -/
def presheafDensityJointRestriction : leftUnstraighteningTransformationSpace H G ⟶
    leftUnstraighteningTransformationSpace (presheafDensityEvaluationDiagram F x)
      (SSet.const (presheafDensityEvaluationVertex F x)) :=
  intervalMappingPostOfEq
    ((pre ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))).app
      SpaceInfinity) (functorVertex H) (functorVertex G)
    (congrArg functorVertex (presheafDensitySourceInclusion_source F x))
    (congrArg functorVertex (presheafDensitySourceInclusion_target F x))

/-- 元の c1 の変換頂点を制限すると、同じ元の密度変換の評価に一致する。 -/
lemma presheafDensityJointRestriction_vertex :
    (presheafDensityJointRestriction F x).app (Opposite.op ⦋0⦌)
      ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (presheafDensityTransformation F).realization.transformation)) =
      presheafDensityEvaluatedTransformationVertex F x := by
  have ht : homotopyTransformationVertex (presheafDensityJointHomotopy F) =
      (smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (presheafDensityTransformation F).realization.transformation) :=
    homotopyTransformationVertex_recovered _
  rw [← ht]
  exact (homotopyTransformationVertex_restriction (presheafDensityJointHomotopy F)
    ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
    (presheafDensitySourceInclusion_source F x) (presheafDensitySourceInclusion_target F x)
    (presheafDensityRestrictedHomotopy F x) rfl).trans
      (presheafDensityEvaluatedTransformationVertex_restriction F x).symm

end SerrePositivity.InfinityCategories.F2.Ind
