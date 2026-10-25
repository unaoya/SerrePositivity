module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Edge

/-!
概要：strict 図式の coherent ホモロジー図式は元のホモロジー関手と自然同型。
方針：閉零 nerve の辺を元の加群射へ戻す。
規約：coherent C1 の特殊化としてのみ strict 性を使う。
使われ方：strict 標準増大のホモロジー射の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J] (F : J ⥤ ModuleCategory R D)

lemma dgCoherentBarStrictDiagramEdge {j k : J} (f : j ⟶ k) :
    dgCoherentBarDiagramEdge R D (dgCoherentBarStrictDiagram R D F) f = F.map f := by
  apply (closedHomEquiv R (RightModule R D) (F.obj j) (F.obj k)).injective
  unfold dgCoherentBarDiagramEdge
  erw [DGNerve.HomotopyComparison.edgeClosed_cycle]
  apply Subtype.ext
  exact closedNerveHom_zero _

def dgCoherentBarStrictHomologyDiagramIso (x : D) (q : ℤ) :
    dgCoherentBarHomologyDiagram R D (dgCoherentBarStrictDiagram R D F) x q ≅
      F ⋙ moduleEvaluation R D x ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q :=
  NatIso.ofComponents
    (fun j => dgCoherentBarHomologyDiagramObjIso R D (dgCoherentBarStrictDiagram R D F) x q j)
    (fun f => by
      have h := dgCoherentBarHomologyDiagramObjIso_naturality R D
        (dgCoherentBarStrictDiagram R D F) x q f
      rw [dgCoherentBarStrictDiagramEdge] at h
      exact h)

end SerrePositivity.InfinityCategories
