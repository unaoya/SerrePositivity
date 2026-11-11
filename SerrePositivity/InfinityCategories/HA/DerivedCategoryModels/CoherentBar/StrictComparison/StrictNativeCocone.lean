module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits

/-!
概要：指定 strict 余錐を同じ coherent 図式の native 余錐にする。
方針：小さい WithTerminal 形状の指定余錐を宇宙移送し、元の拡張関手を後合成する。
規約：余極限性をここでは主張せず、同じ全余錐を構成する。
使われ方：実分解後の指定 strict 余錐との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

def dgBarCoconeExtendedFunctor (c : Cocone F) : WithTerminal J ⥤ ModuleCategory R D :=
  WithTerminal.lift F c.ι.app (fun _ _ f => c.w f)

def dgBarTerminalNativeCocone (R : Type u) (D : Type v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{max (u + 1) v, u}).map
      (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone J)).ulift

lemma dgBarStrictExtendedDiagram_restrict (c : Cocone F) :
    (SSet.uliftFunctor.{max (u + 1) v, u}).map
        (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F := rfl

def dgBarStrictNativeCocone (c : Cocone F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) :=
  ⟨(dgBarTerminalNativeCocone R D (J := J)).val ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c), by
    rw [← Category.assoc, (dgBarTerminalNativeCocone R D (J := J)).property,
      dgBarStrictExtendedDiagram_restrict]⟩

lemma dgBarStrictNativeCocone_vertex (c : Cocone F) :
    (dgBarStrictNativeCocone R D F c).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex R) c.pt) := by
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c)).app _
    (dgBarTerminalNativeCocone R D (J := J)).vertex = _
  dsimp only [dgBarTerminalNativeCocone]
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_vertex]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone J).pt) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
