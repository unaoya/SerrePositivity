module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ExtendedCoconeVertexMaps
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ExtendedHomologyRestriction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoconeHomologyLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexHomologyTransportGeneral

/-!
概要：coherent 拡張図式の native 余錐のホモロジーは、同じ拡張ホモロジー余錐。
方針：回収する実頂点射と元の指定終頂点射の自然性を使う。
規約：同じ頂点・同じ全脚を保つ。
使われ方：分解後の native 余錐のホモロジー余極限性を回収する。
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
  {J : Type u} [PartialOrder J]
  (A : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve (WithTerminal J)) ⟶
    dgNerve R (RightModule R D))

def dgBarExtendedCoconeHomologyPointIso (x : D) (q : ℤ) :
    (dgCoherentCoconeHomology R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) x q).pt ≅
        (dgCoherentBarHomologyDiagram R D A x q).obj WithTerminal.star :=
  dgBarVertexHomologyTransportIso R D A x q
    (dgCoherentBarCoconeModule R D (dgBarExtendedBaseDiagram R D A) (dgBarExtendedNativeCocone R D A))
    WithTerminal.star (dgBarExtendedNativeCocone_module R D A)

lemma dgBarExtendedCoconeHomology_leg (x : D) (q : ℤ) (j : J) :
    (dgCoherentCoconeHomology R D (dgBarExtendedBaseDiagram R D A)
        (dgBarExtendedNativeCocone R D A) x q).ι.app j ≫
      (dgBarExtendedCoconeHomologyPointIso R D A x q).hom =
        (dgCoherentBarHomologyDiagram R D A x q).map (WithTerminal.homFrom j) := by
  rw [← cancel_epi (dgCoherentBarSourceHomologyIso R D
    (dgBarExtendedBaseDiagram R D A) x q 0 (nerveEquiv.symm j)).hom]
  rw [← Category.assoc]
  erw [dgCoherentCoconeHomology_source_leg R D (dgBarExtendedBaseDiagram R D A)
    (dgBarExtendedNativeCocone R D A) x q (nerveEquiv.symm j)]
  exact dgBarVertexHomologyTransport_naturality R D A x q
    (dgBarExtendedSource_vertex R D A j) (dgBarExtendedNativeCocone_module R D A)
    _ (WithTerminal.homFrom j) (dgBarExtendedCoconeVertexMap_naturality R D A j)

def dgBarExtendedCoconeHomologyIso (x : D) (q : ℤ) :
    dgCoherentCoconeHomology R D (dgBarExtendedBaseDiagram R D A)
        (dgBarExtendedNativeCocone R D A) x q ≅
      (Cocone.precompose ((dgBarExtendedHomologyRestrictionIso R D A x q).hom)).obj
        (dgBarTerminalHomologyCocone R (dgCoherentBarHomologyDiagram R D A x q)) :=
  by
    refine Cocone.ext (dgBarExtendedCoconeHomologyPointIso R D A x q) ?_
    intro j
    simpa only [Cocone.precompose_obj_ι, NatTrans.comp_app, dgBarExtendedHomologyRestrictionIso,
      NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp] using!
      dgBarExtendedCoconeHomology_leg R D A x q j

def dgBarExtendedCoconeHomologyIsColimit (x : D) (q : ℤ)
    (h : IsColimit (dgBarTerminalHomologyCocone R (dgCoherentBarHomologyDiagram R D A x q))) :
    IsColimit (dgCoherentCoconeHomology R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) x q) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (dgBarExtendedHomologyRestrictionIso R D A x q) _).symm h)
    (dgBarExtendedCoconeHomologyIso R D A x q).symm

end SerrePositivity.InfinityCategories
