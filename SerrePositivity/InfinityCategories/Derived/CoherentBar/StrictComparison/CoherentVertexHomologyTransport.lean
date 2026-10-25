module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixEdgeClosed

/-!
概要：元の頂点加群との等号を保持した H(G) の係数同型と自然性。
方針：等号射の実ホモロジー同型とホモトピー圏を経たホモロジー同型を合成する。
規約：実加群射の可換式から係数自然性を導く。
使われ方：一次 prefix の係数を通常のホモロジー bar の辺へ合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentBarVertexHomologyTransportIso (x : D) (r : ℤ) (M : RightModule R D) (j : J)
    (h : M = coherentDiagramVertex G (nerveEquiv.symm j)) :
    (M.obj (Opposite.op x)).homology r ≅ (dgCoherentBarHomologyDiagram R D G x r).obj j :=
  HomologicalComplex.homologyMapIso ((moduleEvaluation R D x).mapIso
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) h))) r ≪≫
      (dgCoherentBarHomologyDiagramObjIso R D G x r j).symm

lemma dgCoherentBarVertexHomologyTransport_naturality (x : D) (r : ℤ)
    {M N : RightModule R D} {j k : J}
    (hM : M = coherentDiagramVertex G (nerveEquiv.symm j))
    (hN : N = coherentDiagramVertex G (nerveEquiv.symm k))
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N) (g : j ⟶ k)
    (h : f ≫ eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hN) =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hM) ≫ dgCoherentBarDiagramEdge R D G g) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) r ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x r N k hN).hom =
    (dgCoherentBarVertexHomologyTransportIso R D G x r M j hM).hom ≫
      (dgCoherentBarHomologyDiagram R D G x r).map g := by
  have he := congrArg (fun a => HomologicalComplex.homologyMap ((moduleEvaluation R D x).map a) r) h
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp] at he
  have hn := dgCoherentBarHomologyDiagramObjIso_naturality R D G x r g
  have hi : HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (dgCoherentBarDiagramEdge R D G g)) r ≫
        (dgCoherentBarHomologyDiagramObjIso R D G x r k).inv =
      (dgCoherentBarHomologyDiagramObjIso R D G x r j).inv ≫
        (dgCoherentBarHomologyDiagram R D G x r).map g := by
    rw [← cancel_epi (dgCoherentBarHomologyDiagramObjIso R D G x r j).hom,
      ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  simp only [dgCoherentBarVertexHomologyTransportIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [← Category.assoc, he, Category.assoc, hi]
  rw [Category.assoc]

end SerrePositivity.InfinityCategories
