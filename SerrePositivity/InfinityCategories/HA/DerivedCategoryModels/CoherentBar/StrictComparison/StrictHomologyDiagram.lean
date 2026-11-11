module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Edge

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

lemma dgCoherentBarStrictDiagramEdge {j k : J} (f : j ⟶ k) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDiagramEdge R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) f = F.map f := by
  apply (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (F.obj j) (F.obj k)).injective
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDiagramEdge
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero _

def dgCoherentBarStrictHomologyDiagramIso (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q ≅
      F ⋙ _root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q :=
  NatIso.ofComponents
    (fun j => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q j)
    (fun f => by
      have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso_naturality R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q f
      rw [dgCoherentBarStrictDiagramEdge] at h
      exact h)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
