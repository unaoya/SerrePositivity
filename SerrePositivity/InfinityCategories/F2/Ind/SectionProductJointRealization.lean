module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductDiagonalRealization
public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductClassification
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedClassificationRealization

/-!
概要：全単体切断の元の積図式の実現と、実際の共同分類の初頂点制限を比較する。
方針：対角評価を全単体で同定し、同じ weighted 分類の大域同型と復元単位を合成する。
規約：同じ添字全体の実現の比較を保持する。
使われ方：strict 分類像へ局所化から戻すための全高次の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open scoped Simplicial
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I J : Type u} [Category.{u} I] [Category.{u} J] {B : SSet.{u}}
  (F : I ⥤ LeftFibrationObject B)

/-- 元の添字と相対定義域を同時に動かす、同じ Kan 図式値の族の共同実現。 -/
def sectionProductJointRealization (A : Jᵒᵖ ⥤ Over B) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (I × J)) ⟶ SpaceInfinity.{u} :=
  lift ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.snd I J)))
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.fst I J)) ≫
      HomotopyLimits.strictCoherentDiagram (strictLeftSectionKanDiagramFamily F A)) ≫
    kanDiagramJointEvaluation J

/-- 共同実現は元の積添字の切断図式の全 coherent 表示と厳密に一致する。 -/
lemma sectionProductJointRealization_eq (A : Jᵒᵖ ⥤ Over B) :
    sectionProductJointRealization F A =
      kanDiagramCoherentNerve (strictLeftSectionProductDiagram F A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  let d := (⟨ULift.down, fun _ _ h ↦ h⟩ :
    ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor
  exact sectionProductDiagonalRealization F A
    (d ⋙ σ ⋙ CategoryTheory.Prod.fst I J) (d ⋙ σ ⋙ CategoryTheory.Prod.snd I J)

/-- 元の共同分類の初頂点制限を、元の全切断図式そのものの実現へ移す一つの大域同型。 -/
def sectionProductClassificationRealizationIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (sectionProductBaseMap I B) ≫
        leftStraighteningInfinityDiagram (leftFibrationWeightedProjection F))
      (sectionProductJointRealization F (transportSimplexDomainFunctor B)) := by
  rw [sectionProductJointRealization_eq]
  exact sectionProductClassificationIso F ≪≫
    weightedClassificationRealizationIso (strictLeftTransportSectionDiagram F)

end SerrePositivity.InfinityCategories.F2.Ind
