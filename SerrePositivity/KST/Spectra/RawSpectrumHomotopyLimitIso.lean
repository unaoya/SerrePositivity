module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitLevelLimit
public import SerrePositivity.KST.Spectra.RawSpectrumMappingLimits
public import SerrePositivity.KST.Spectra.RawSpectrumWeightedDiagram

/-!
概要：元の全整合写像空間と段ごとの homotopy end の厳密な交換同型。
方針：元の weighted wedge の各段の極限性を Hom で保存し、二変数図式の交換同型を合成する。
規約：全単体と基点を保持する。使われ方：BF homotopy limit の豊穣 Hom と γ3 の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawHomotopyEndSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I] (X : OmegaSpectrum.{u}) (D : I ⥤ KanSequence.{u})

/-- 元の homotopy end の wedge に点つき Hom を施した実際の wedge。 -/
def homotopyLimitMappingWedge : Wedge
    (EndRightAdjoint.postDiagram (pointedFunctor X)
      (KanSequence.weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D)) :=
  (KanSequence.homotopyLimitWedge D).map (pointedFunctor X)

/-- 元の homotopy end の wedge は、点つき Hom の後でも実際に極限。 -/
def homotopyLimitMappingWedge_isLimit : IsLimit (homotopyLimitMappingWedge X D) :=
  ((KanSequence.homotopyLimitWedge D).isLimitMapEquiv (pointedFunctor X))
    (isLimitOfLevelLimits X (KanSequence.homotopyLimitWedge D)
      (KanSequence.homotopyLimitWedge_level_isLimit D))

/-- 元の全写像空間と、写像空間を施した weighted Hom 図式の end の同型。 -/
def homotopyLimitMappingEndIso :
    pointedSpace X (KanSequence.homotopyLimit D) ≅
      end_ (EndRightAdjoint.postDiagram (pointedFunctor X)
        (KanSequence.weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D)) :=
  (homotopyLimitMappingWedge_isLimit X D).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
lemma homotopyLimitMappingEndIso_hom_π (i : I) :
    (homotopyLimitMappingEndIso X D).hom ≫
        end_.π (EndRightAdjoint.postDiagram (pointedFunctor X)
          (KanSequence.weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D)) i =
      pointedPost X (KanSequence.homotopyLimitEvaluation D i) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (homotopyLimitMappingWedge_isLimit X D) (limit.isLimit _) (.left i)

/-- 元の点つき Hom と homotopy end の、実際の厳密な交換同型。 -/
def homotopyLimitIso :
    pointedSpace X (KanSequence.homotopyLimit D) ≅
      PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ pointedFunctor X) :=
  homotopyLimitMappingEndIso X D ≪≫ weightedDiagramEndIso X (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D

/-- 交換同型の順射は、元の射影による後合成と既存の cotensor 交換で計算される。 -/
@[reassoc]
lemma homotopyLimitIso_hom_π (i : I) :
    (homotopyLimitIso X D).hom ≫
        end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ pointedFunctor X)) i =
      pointedPost X (KanSequence.homotopyLimitEvaluation D i) ≫
        (cotensorIso X (D.obj i) (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).hom := by
  change ((homotopyLimitMappingEndIso X D).hom ≫
      end_.map (weightedDiagramIso X (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D).hom) ≫ end_.π _ i = _
  rw [Category.assoc, end_.map_π, ← Category.assoc, homotopyLimitMappingEndIso_hom_π]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
