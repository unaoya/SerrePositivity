module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalHomologyCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyCocone

/-!
概要：元の strict 余極限余錐の拡張ホモロジー余錐は余極限。
方針：指定された全脚の C1 比較と新終頂点の評価同型で照合する。
規約：filtered 完全性は元の strict 加群余極限にのみ使う。
使われ方：分解済み coherent 余錐のホモロジー余極限性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

abbrev dgBarColimitExtendedHomologyDiagram (x : D) (q : ℤ) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F))) x q

def dgBarColimitTerminalHomologyCoconeIso (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyCocone R (dgBarColimitExtendedHomologyDiagram R D F x q) ≅
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCocone R D F x q :=
  Cocone.ext (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))
    x q WithTerminal.star) (by
    intro j
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCocone_leg]
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso_naturality R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))
      x q (WithTerminal.homFrom j)
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagramEdge] at h
    exact h)

def dgBarColimitTerminalHomologyIsColimit (x : D) (q : ℤ) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyCocone R
      (dgBarColimitExtendedHomologyDiagram R D F x q)) :=
  IsColimit.ofIsoColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCoconeIsColimit R D F x q)
    (dgBarColimitTerminalHomologyCoconeIso R D F x q).symm

def dgBarResolvedColimitExtendedHomologyIso (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarResolvedCoherentDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))) x q ≅
      dgBarColimitExtendedHomologyDiagram R D F x q :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarResolvedCoherentHomologyIso R D _ x q

def dgBarResolvedColimitTerminalHomologyIsColimit (x : D) (q : ℤ) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyCocone R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarResolvedCoherentDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))) x q)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyIsColimit_of_iso R (dgBarResolvedColimitExtendedHomologyIso R D F x q)
    (dgBarColimitTerminalHomologyIsColimit R D F x q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
