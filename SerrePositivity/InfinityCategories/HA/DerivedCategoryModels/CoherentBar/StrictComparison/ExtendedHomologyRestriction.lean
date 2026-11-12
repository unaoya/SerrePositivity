module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedNativeCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalHomologyCocone

/-!
概要：終頂点付加図式の coherent ホモロジーを元の添字へ制限する。
方針：添字 nerve の同じ頂点と辺の像を照合する。
規約：strict 性は仮定しない。
使われ方：native 余錐のホモロジー余錐と拡張図式の余錐の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (A : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve (WithTerminal J)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgBarExtendedHomotopyDiagram_restrict :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomotopyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedBaseDiagram R D A) =
      (WithTerminal.incl : J ⥤ WithTerminal J) ⋙ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomotopyDiagram R D A := by
  have hi : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarIndexHomotopyFunctor.{u, max (u + 1) v} J ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map ((SSet.uliftFunctor.{max (u + 1) v, u}).map
        (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J))) =
      (WithTerminal.incl : J ⥤ WithTerminal J) ⋙
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarIndexHomotopyFunctor.{u, max (u + 1) v} (WithTerminal J) := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change SSet.Truncated.HomotopyCategory₂.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, max (u + 1) v} (X := nerve J)
        (CategoryTheory.nerve.edgeMk f).toTruncated).map
          ((SSet.truncation 2).map ((SSet.uliftFunctor.{max (u + 1) v, u}).map
            (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J))))) =
      SSet.Truncated.HomotopyCategory₂.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, max (u + 1) v} (X := nerve (WithTerminal J))
          (CategoryTheory.nerve.edgeMk (WithTerminal.incl.map f)).toTruncated)
    congr 1
    apply SSet.Truncated.Edge.ext
    change ULift.up ((nerveMap WithTerminal.incl).app _ (CategoryTheory.nerve.edgeMk f).edge) = _
    exact congrArg ULift.up (nerveMap_app_mk₁ WithTerminal.incl f)
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomotopyDiagram, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedBaseDiagram,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_comp, Functor.assoc] using!
    congrArg (fun F => F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map A ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R (RightModule R D)) hi

lemma dgBarExtendedHomologyDiagram_restrict (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedBaseDiagram R D A) x q =
      (WithTerminal.incl : J ⥤ WithTerminal J) ⋙ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D A x q := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram]
  rw [dgBarExtendedHomotopyDiagram_restrict]
  rfl

def dgBarExtendedHomologyRestrictionIso (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarExtendedBaseDiagram R D A) x q ≅
      (WithTerminal.incl : J ⥤ WithTerminal J) ⋙ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D A x q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    have h := (eqToHom (dgBarExtendedHomologyDiagram_restrict R D A x q)).naturality f
    simpa only [eqToHom_app, eqToHom_refl, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using! h)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
