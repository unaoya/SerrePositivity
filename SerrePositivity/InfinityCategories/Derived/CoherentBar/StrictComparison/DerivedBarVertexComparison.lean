module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictAugmentationQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactClassicalTransport

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)

def dgKappaStrictDerivedBarCocone_vertexIso (c : Cocone F) (hc : IsColimit c) :
    VertexIso (dgKappaStrictDerivedBarCocone R D F).vertex
      (dgConeModuleDerivedVertex R D c.pt) := by
  rw [dgKappaStrictDerivedBarCocone_vertex]
  exact dgConeModuleDerivedVertexIsoOfDerivedIso R D
    (moduleDerivedIso R D (dgCoherentBarStrictColimitAugmentation R D F)
      (dgCoherentBarStrictColimitAugmentation_quasiIso R D F) ≪≫
      (moduleToDerived R D).mapIso ((colimit.isColimit F).coconePointUniqueUpToIso hc))

end SerrePositivity.InfinityCategories
