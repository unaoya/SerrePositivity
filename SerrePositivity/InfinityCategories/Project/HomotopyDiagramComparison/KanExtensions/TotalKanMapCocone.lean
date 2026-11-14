module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ConstantCoconeHomotopyComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalMapCocone

/-!
概要：元の余極限 Kan 模型の射を、元の単位を使う native 余錐全体へ移す。
方針：指定射へ元の全空間の単位を前合成し、頂点表示の標準等式だけを続ける。
規約：Kan 射の辺に沿う native 余錐輸送との同定は別。使われ方：両脚の単位表現の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の余極限 Kan 射に元の全空間の単位を前合成した、指定頂点の値への射。 -/
def totalKanMapCoconeInput (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) ≫ a ≫
    eqToHom (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object G).symm

/-- 元の Kan 射の単位表現から実現した、同じ図式上の native 余錐。 -/
def totalKanMapCocone (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (totalKanMapCoconeInput F G a)

/-- 単位表現の余錐の頂点は、標的図式の元の余極限頂点。 -/
lemma totalKanMapCocone_vertex (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G) :
    (totalKanMapCocone F G a).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone_vertex _ _ _

/-- 元の全空間射の Kan 置換にホモトピックなら、単位表現の全余錐は元の写像余錐と同型。 -/
def totalKanMapCoconeIso
    {a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G}
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G)
    (H : SSet.Homotopy a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map m)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (totalKanMapCocone F G a) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (totalKanMapCocone_vertex F G a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone F G m) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone_vertex F G m)) := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)))
    (eqToHom (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object G).symm)
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map m) ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object G).symm =
      m ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality m]
    rfl
  let U : SSet.Homotopy (totalKanMapCoconeInput F G a) (m ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G) :=
    { h := T.h, h₀ := T.h₀, h₁ := T.h₁.trans ht, rel := T.rel }
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantCoconeHomotopyIso F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) U

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
