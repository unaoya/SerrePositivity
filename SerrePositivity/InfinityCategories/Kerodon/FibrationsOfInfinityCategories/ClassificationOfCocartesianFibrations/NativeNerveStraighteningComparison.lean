module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportComparison

/-!
概要：通常のnerve上の同じ射影のnative分類とstrict transportの分類を比較する。
方針：同じ既存の相対表現への二つの全関手同型を合成する。
規約：点ごとのfiber同値を全図式の自然性の代用にしない。
使われ方：Grothendieck–Kanの全分類から元のKan係数への復元。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 同じnerve上の射影の二つの分類を、同じ相対表現を経由して比較する。 -/
def leftStraighteningInfinityDiagram_nerveCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningCandidate p) :=
  (leftStraighteningInfinityDiagram_representationIso p (nerveLeftTransportRepresentation p)).trans
    (nerveStraighteningRepresentationIso p (nerveLeftTransportRepresentation p)).symm

local instance kanObjectDiagram_kanComplex {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) (c : C) : KanComplex ((F ⋙ kanObjectForget).obj c) :=
  (F.obj c).isKanComplex

/-- 元のKan係数の標準単位を、nativeな全分類からの全関手同型へつなぐ。 -/
def weightedNerveNativeStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningInfinityDiagram (weightedNerveProjection (F ⋙ kanObjectForget))) :=
  (weightedNerveStraighteningUnitIso F).trans
    (leftStraighteningInfinityDiagram_nerveCandidateIso
      (weightedNerveProjection (F ⋙ kanObjectForget))).symm
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
