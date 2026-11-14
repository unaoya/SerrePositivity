module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarDiagram
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleKappaCompactClassicalTransport

/-!
概要：C1 の同じ標準射が、実導来 bar 余錐の頂点と strict 余極限の頂点を同型にする。
方針：実 dg 加群擬同型を主導来同型に送り、正本の半自由模型で頂点同型へ戻す。
規約：図式の全単体は DerivedBarDiagram の同じ図式で固定する。
使われ方：実導来像の native 余極限性から比較述語の値を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

def dgKappaStrictDerivedBarCocone_vertexIso (c : Cocone F) (hc : IsColimit c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone R D F).vertex
      (dgConeModuleDerivedVertex R D c.pt) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D
    (moduleDerivedIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation_quasiIso R D F) ≪≫
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).mapIso ((colimit.isColimit F).coconePointUniqueUpToIso hc))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
