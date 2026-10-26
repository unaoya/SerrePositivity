module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.TerminalNativeLeg
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyDiagram

/-!
概要：coherent な終頂点付加図式から、指定された native 余錐を回収する。
方針：小さい終頂点付加余錐を同じ全 coherent 図式で後合成する。
規約：strict 性は仮定しない。
使われ方：分解後の strict 余錐の全 native データとホモロジーの照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (A : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve (WithTerminal J)) ⟶
    dgNerve R (RightModule R D))

abbrev dgBarExtendedBaseDiagram :=
  (SSet.uliftFunctor.{max (u + 1) v, u}).map
    (nerveMap (WithTerminal.incl : J ⥤ WithTerminal J)) ≫ A

def dgBarExtendedNativeCocone : JoinCocone (dgBarExtendedBaseDiagram R D A) :=
  ⟨(dgBarTerminalNativeCocone R D (J := J)).val ≫ A, by
    rw [← Category.assoc, (dgBarTerminalNativeCocone R D (J := J)).property]⟩

lemma dgBarExtendedNativeCocone_vertex :
    (dgBarExtendedNativeCocone R D A).vertex =
      A.app (Opposite.op ⦋0⦌) (ULift.up (nerveEquiv.symm WithTerminal.star)) := by
  change A.app _ (dgBarTerminalNativeCocone R D (J := J)).vertex = _
  rw [dgBarTerminalNativeCocone, JoinCocone.ulift_vertex, F1B.nerveCocone_vertex]
  rfl

lemma dgBarExtendedNativeCocone_simplex_zero (j : J) :
    dgCoherentBarCoconeSimplex R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) (nerveEquiv.symm j) =
        coherentDiagramSimplex A (ComposableArrows.mk₁ (WithTerminal.homFrom j)) := by
  change SSet.yonedaEquiv
    (((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm (ULift.up (nerveEquiv.symm j))) (𝟙 Δ[0]) ≫
        (dgBarTerminalNativeCocone R D (J := J)).val) ≫ A) = _
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, dgBarJoinIntervalIdentity]
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
  erw [F1B.joinCoconeLegSimplex_natural, SSet.yonedaEquiv_symm_app_id,
    dgBarTerminalNativeCocone_leg R D j]
  rfl

lemma dgBarExtendedNativeCocone_module :
    dgCoherentBarCoconeModule R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) = coherentDiagramVertex A (nerveEquiv.symm WithTerminal.star) := by
  change (dgBarExtendedNativeCocone R D A).vertex.obj 0 = _
  rw [dgBarExtendedNativeCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories
