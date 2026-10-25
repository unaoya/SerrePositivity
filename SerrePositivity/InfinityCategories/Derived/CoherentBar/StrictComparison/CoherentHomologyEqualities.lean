module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyFaceIndices

/-!
概要：raw 単体ラベル・頂点添字の等号に対する shift ホモロジー比較の自然性。
方針：等号を消去し、同じホモロジー同型と関手の単位則へ戻す。
規約：実等号射と全整数次数を保持する。
使われ方：一次 prefix の後尾ラベルを零番の面の係数へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgCoherentBarFamilyShiftHomology_transport {I : SSet.{u}}
    (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
    {s t : dgCoherentBarIndex I} (h : s = t) (x : D) (p r : ℤ)
    (hs : (s.1 : ℤ) + p = r) (ht : (t.1 : ℤ) + p = r) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (eqToHom (congrArg (dgCoherentBarFamily R D G) h))) p ≫
      (dgComplexShiftHomologyIso R ((dgCoherentBarSource R D G t).obj (Opposite.op x))
        (t.1 : ℤ) p r ht).hom =
    (dgComplexShiftHomologyIso R ((dgCoherentBarSource R D G s).obj (Opposite.op x))
      (s.1 : ℤ) p r hs).hom ≫
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (eqToHom (congrArg (ForgetEnrichment.of (Complex R))
          (congrArg (dgCoherentBarSource R D G) h)))) r := by
  cases h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

lemma dgCoherentBarVertexHomologyTransport_equalities {J : Type u} [PartialOrder J]
    (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      dgNerve R (RightModule R D))
    (x : D) (r : ℤ) {M N : RightModule R D} (hMN : M = N)
    {j k : J} (hjk : j = k)
    (hM : M = coherentDiagramVertex G (nerveEquiv.symm j))
    (hN : N = coherentDiagramVertex G (nerveEquiv.symm k)) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hMN))) r ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x r N k hN).hom =
    (dgCoherentBarVertexHomologyTransportIso R D G x r M j hM).hom ≫
      (dgCoherentBarHomologyDiagram R D G x r).map (eqToHom hjk) := by
  cases hMN
  cases hjk
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories
