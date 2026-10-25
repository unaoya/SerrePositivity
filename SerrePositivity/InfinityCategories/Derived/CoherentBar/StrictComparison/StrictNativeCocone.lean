module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeExtension
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeVertex
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J] (F : J ⥤ ModuleCategory R D)

def dgBarCoconeExtendedFunctor (c : Cocone F) : WithTerminal J ⥤ ModuleCategory R D :=
  WithTerminal.lift F c.ι.app (fun _ _ f => c.w f)

def dgBarTerminalNativeCocone (R : Type u) (D : Type v) :
    JoinCocone ((SSet.uliftFunctor.{max (u + 1) v, u}).map
      (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J))) :=
  (F1B.nerveCoconeEquiv (F1B.withTerminalCocone J)).ulift

lemma dgBarStrictExtendedDiagram_restrict (c : Cocone F) :
    (SSet.uliftFunctor.{max (u + 1) v, u}).map
        (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J)) ≫
      dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c) =
        dgCoherentBarStrictDiagram R D F := rfl

def dgBarStrictNativeCocone (c : Cocone F) : JoinCocone (dgCoherentBarStrictDiagram R D F) :=
  ⟨(dgBarTerminalNativeCocone R D (J := J)).val ≫
      dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c), by
    rw [← Category.assoc, (dgBarTerminalNativeCocone R D (J := J)).property,
      dgBarStrictExtendedDiagram_restrict]⟩

lemma dgBarStrictNativeCocone_vertex (c : Cocone F) :
    (dgBarStrictNativeCocone R D F c).vertex =
      Simplex.vertex (ForgetEnrichment.to (Complex R) c.pt) := by
  change (dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c)).app _
    (dgBarTerminalNativeCocone R D (J := J)).vertex = _
  dsimp only [dgBarTerminalNativeCocone]
  rw [JoinCocone.ulift_vertex, F1B.nerveCocone_vertex]
  apply (dgNerve.vertexEquiv R (RightModule R D)).injective
  change coherentDiagramVertex
    (dgCoherentBarStrictDiagram R D (dgBarCoconeExtendedFunctor R D F c))
    (nerveVertex (F1B.withTerminalCocone J).pt) = _
  rw [dgCoherentBarStrictDiagram_vertex]
  rfl

end SerrePositivity.InfinityCategories
