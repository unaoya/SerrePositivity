module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedFibrationTransport
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SectionsFiberwiseEquivalence

/-!
概要：同じ底上のleft fibrationの全分類同型を、元の切断空間の実際の同値へ戻す。
方針：共通の小さいunstraighteningへ厳密な底上の比較を二本作り、相対後合成の同値を合成する。
規約：IS-W2 R03b。底・二つの元の射影を固定し、fiberごとの分類で代用しない。
使われ方：元のBE TotのBK係数からnative錐の切断模型への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] simplicialSections_kanComplex

/-- 同じ底を保つ前合成同値の後合成は、元の切断写像そのものの同値。 -/
theorem simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsQCatEquivalence (simplicialSectionsMap f hf) := by
  have hp := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso p)).isQCatEquivalence
  have hq := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso q)).isQCatEquivalence
  apply hq.cancel_right
  change IsQCatEquivalence (simplicialSectionsMap f hf ≫ (simplicialSectionsRelativeIso q).hom)
  rw [simplicialSectionsRelativeIso_naturality]
  exact hp.comp (relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q f hf ef (𝟙 B))

/-- 同じ全分類の同型を、元の二つの切断空間の同値へ戻す。 -/
def classifiedLeftFibrationSectionsEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) :
    QCatEquivalence (simplicialSections p) (simplicialSections q) := by
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let f := classifiedFibrationTransport p q η
  have hf : f ≫ r = p := classifiedFibrationTransport_projection p q η
  have ef : IsPrecompositionEquivalence f :=
    classifiedFibrationTransport_isPrecompositionEquivalence p q η
  let g := leftStraighteningInfinityReconstruction q
  have hg : g ≫ r = q := leftStraighteningInfinityReconstruction_projection q
  have eg : IsPrecompositionEquivalence g :=
    leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q
  have hfr := simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence p r f hf ef
  have hgr := simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence q r g hg eg
  exact hfr.choose.trans hgr.choose.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
