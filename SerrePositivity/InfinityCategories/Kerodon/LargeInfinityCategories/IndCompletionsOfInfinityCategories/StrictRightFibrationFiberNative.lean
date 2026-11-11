module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationFiberCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanCocone

/-!
概要：strict right fibration 余極限の元の fiber 余錐は SpaceInfinity の余極限。
方針：元の fiber 図式と余錐を Kan 対象に束ね、filtered Kan 余極限の判定を適用する。
規約：元の余錐の全脚と高次の整合性を保った native な余極限性。
使われ方：coherent な前層余錐への点ごとの比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 元の各 right fiber を Kan 対象として束ねた同じ図式。 -/
def rightFibrationFiberKanDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj i := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (F.obj i).val.hom b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex _ _⟩
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberDiagram F b).map f
  map_id i := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberDiagram F b).map_id i
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberDiagram F b).map_comp f g

/-- Kan 図式の台は元の同じ fiber 図式。 -/
lemma rightFibrationFiberKanDiagram_forget (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    rightFibrationFiberKanDiagram F b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberDiagram F b := rfl

variable [IsFiltered I]

/-- 同じ strict 余極限の実際の fiber を Kan 対象に束ねる。 -/
def strictRightFibrationColimitFiberKanObject (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex _ _⟩

/-- 元の全空間の余極限の脚から得た同じ Kan 余錐。 -/
def strictRightFibrationFiberKanCocone (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : Cocone (rightFibrationFiberKanDiagram F b) where
  pt := strictRightFibrationColimitFiberKanObject F b
  ι := { app i := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationFiberColimitCocone F b).ι.app i
         naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationFiberColimitCocone F b).ι.naturality f }

/-- Kan 余錐の台は同じ実際の fiber 余錐。 -/
lemma strictRightFibrationFiberKanCocone_forget (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone (strictRightFibrationFiberKanCocone F b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationFiberColimitCocone F b := rfl

/-- 同じ元の Kan 余錐の native な余極限性。 -/
lemma strictRightFibrationFiberKanCocone_isColimit (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (strictRightFibrationFiberKanCocone F b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationFiberColimitCocone_isColimit F b)

/-- 元の fiber 図式の標準の coherent 表示上の同じ native 余錐。 -/
def strictRightFibrationFiberNativeCocone (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (rightFibrationFiberKanDiagram F b)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (strictRightFibrationFiberKanCocone F b))

/-- 元の fiber 図式の同じ native 余錐は SpaceInfinity の余極限。 -/
lemma strictRightFibrationFiberNativeCocone_isColimit (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (strictRightFibrationFiberNativeCocone F b) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (strictRightFibrationFiberKanCocone_isColimit F b)

/-- 同じ native 余極限の頂点は元の strict 余極限射影の実際の fiber。 -/
lemma strictRightFibrationFiberNativeCocone_vertex (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) : (strictRightFibrationFiberNativeCocone F b).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (strictRightFibrationColimitFiberKanObject F b) := by
  rw [strictRightFibrationFiberNativeCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
