module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsComparison

/-!
概要：元の切断比較を共通の復元へ送ると、指定分類同型の同じ実写像による切断へ戻る。
方針：同じ後合成の同値の余単位を、元の切断の写像で前合成する。
規約：IS-W2 R03bの既存の余単位則。全単体的写像の関手同型を保持する。
使われ方：指定BK点の像・標準脚の同じ復元中での追跡。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
attribute [local instance] simplicialSections_kanComplex
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

/-- 同じ全切断比較の三角形は、元の指定分類同型を使う復元射で可換。 -/
def classifiedLeftFibrationSectionsEquivalence_triangle :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
          (leftStraighteningInfinityReconstruction_projection q))
      (simplicialSectionsMap (classifiedFibrationTransport p q η)
        (classifiedFibrationTransport_projection p q η)) := by
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let f := classifiedFibrationTransport p q η
  let hf := classifiedFibrationTransport_projection p q η
  let g := leftStraighteningInfinityReconstruction q
  let hg := leftStraighteningInfinityReconstruction_projection q
  let e := (simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence q r g hg
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q)).choose
  change FunctorIso ((simplicialSectionsMap f hf ≫ e.inv) ≫ e.hom)
    (simplicialSectionsMap f hf)
  have h := FunctorIso.precomp e.invHomIso (simplicialSectionsMap f hf)
  simpa only [Category.assoc, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
