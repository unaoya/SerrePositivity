module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedCoherentAugmentation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ExtendedCoconeHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.TerminalHomologyExactness
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SemifreeHomologyColimitCriterion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarVertexComparison

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)

def dgBarDerivedColimitTerminalHomologyIsColimit (x : D) (q : ℤ) :
    IsColimit (dgBarTerminalHomologyCocone R
      (dgCoherentBarHomologyDiagram R D
        (dgBarDerivedCoherentDiagram R D (dgCoherentBarStrictDiagram R D
          (dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))) x q)) :=
  dgBarTerminalHomologyIsColimit_of_iso R (dgBarDerivedCoherentHomologyIso R D _ x q)
    (dgBarColimitTerminalHomologyIsColimit R D F x q)

theorem dgBarStrictDerivedChosenColimit :
    ∃ t : JoinCocone (dgKappaStrictModuleDiagram R D F), IsColimitCone t ∧
      Nonempty (VertexIso t.vertex (dgConeModuleDerivedVertex R D (colimit F))) := by
  let Q := dgBarRightModuleDerived R D
  let G := dgCoherentBarStrictDiagram R D F ≫ Q
  let c : JoinCocone G := mapJoinCocone Q (dgBarStrictNativeCocone R D F (colimit.cocone F))
  have hc : ∀ x q, IsColimit (dgCoherentCoconeHomology R D
      (G ≫ dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))
      (mapJoinCocone (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D))) c) x q) := by
    intro x q
    let A := dgBarDerivedCoherentDiagram R D (dgCoherentBarStrictDiagram R D
      (dgBarCoconeExtendedFunctor R D F (colimit.cocone F)))
    change IsColimit (dgCoherentCoconeHomology R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) x q)
    exact dgBarExtendedCoconeHomologyIsColimit R D A x q
      (dgBarDerivedColimitTerminalHomologyIsColimit R D F x q)
  obtain ⟨t, ht, ⟨e⟩⟩ := dgSemifreeCoherent_vertexComparison_of_homologyColimit R D G c hc
  have hv : c.vertex = dgConeModuleDerivedVertex R D (colimit F) := by
    change Q.app _ (dgBarStrictNativeCocone R D F (colimit.cocone F)).vertex = _
    rw [dgBarStrictNativeCocone_vertex]
    rfl
  exact ⟨t, ht, ⟨e ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hv)⟩⟩

theorem dgBarStrictDerivedColimitComparison (c : Cocone F) (hc : IsColimit c) :
    ∃ t : JoinCocone (dgKappaStrictModuleDiagram R D F), IsColimitCone t ∧
      Nonempty (VertexIso t.vertex (dgConeModuleDerivedVertex R D c.pt)) := by
  obtain ⟨t, ht, ⟨e⟩⟩ := dgBarStrictDerivedChosenColimit R D F
  exact ⟨t, ht, ⟨e ≪≫ dgConeModuleDerivedVertexIsoOfDerivedIso R D
    ((moduleToDerived R D).mapIso ((colimit.isColimit F).coconePointUniqueUpToIso hc))⟩⟩

theorem dgKappaStrictFilteredColimitComparison_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] : DGKappaStrictFilteredColimitComparison R D κ := by
  intro J _ _ F c hc
  letI := isFiltered_of_isCardinalFiltered J κ
  exact dgBarStrictDerivedColimitComparison R D F c hc

end SerrePositivity.InfinityCategories
