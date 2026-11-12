module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedCoherentAugmentation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedCoconeHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalHomologyExactness
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeHomologyColimitCriterion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarVertexComparison

/-!
概要：filtered strict dg 加群余極限と正本の native 導来余極限を比較する。
方針：指定分解のホモロジー自然同型、coherent C1、射影的 bar と B を接続する。
規約：分解後の図式を strict と仮定せず、分解関手の余極限保存も仮定しない。
使われ方：DGKappaStrictFilteredColimitComparison の無条件値と covers。
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

def dgBarDerivedColimitTerminalHomologyIsColimit (x : D) (q : ℤ) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyCocone R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDerivedCoherentDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))) x q)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalHomologyIsColimit_of_iso R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDerivedCoherentHomologyIso R D _ x q)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarColimitTerminalHomologyIsColimit R D F x q)

theorem dgBarStrictDerivedChosenColimit :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram R D F), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.vertex (dgConeModuleDerivedVertex R D (colimit F))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarRightModuleDerived R D
  let G := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F ≫ Q
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone Q (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarStrictNativeCocone R D F (colimit.cocone F))
  have hc : ∀ x q, IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology R D
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D))) c) x q) := by
    intro x q
    let A := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarDerivedCoherentDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))
    change IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedBaseDiagram R D A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedNativeCocone R D A) x q)
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedCoconeHomologyIsColimit R D A x q
      (dgBarDerivedColimitTerminalHomologyIsColimit R D F x q)
  obtain ⟨t, ht, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgSemifreeCoherent_vertexComparison_of_homologyColimit R D G c hc
  have hv : c.vertex = dgConeModuleDerivedVertex R D (colimit F) := by
    change Q.app _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarStrictNativeCocone R D F (colimit.cocone F)).vertex = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarStrictNativeCocone_vertex]
    rfl
  exact ⟨t, ht, ⟨e ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hv)⟩⟩

theorem dgBarStrictDerivedColimitComparison (c : Cocone F) (hc : IsColimit c) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram R D F), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.vertex (dgConeModuleDerivedVertex R D c.pt)) := by
  obtain ⟨t, ht, ⟨e⟩⟩ := dgBarStrictDerivedChosenColimit R D F
  exact ⟨t, ht, ⟨e ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D
    ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).mapIso ((colimit.isColimit F).coconePointUniqueUpToIso hc))⟩⟩

theorem dgKappaStrictFilteredColimitComparison_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictFilteredColimitComparison R D κ := by
  intro J _ _ F c hc
  letI := isFiltered_of_isCardinalFiltered J κ
  exact dgBarStrictDerivedColimitComparison R D F c hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
