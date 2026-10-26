module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoconeHomologyLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroLayerHomologyAugmentation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictZeroLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegAugmentationLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentBarQuasiIsoCriterion

/-!
概要：native 余錐の実増大のホモロジーは、同じホモロジー余錐の標準増大。
方針：零次元層の各係数で照合し、C1 の実余核性で擬同型判定する。
規約：元の coherent 図式と指定 native 余錐を固定する。
使われ方：分解済み strict 余錐の native 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgNerve R (RightModule R D))

lemma dgBarCoconeUniversal_zeroLayer_homology (c : JoinCocone G) (x : D) (q : ℤ) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (dgBarZeroLayerInclusion R D G ≫ dgCoherentBarCoconeUniversalMap R D G
        (dgCoherentBarMaurerCartan_unconditional R D G) c)) q =
    (dgCoherentBarNaturalLayerHomologyIso R D G x 0 q q (by omega)).hom ≫
      dgHomologyBarNondegAugmentation R (dgCoherentBarHomologyDiagram R D G x q)
        (dgCoherentCoconeHomology R D G c x q) := by
  let P := dgModuleCoproductHomologyIso R D (dgCoherentBarLayerFamily R D G 0) x q
  rw [← cancel_epi P.inv]
  apply Sigma.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (dgCoherentBarLayerIndexEquiv (nerve J) 0).surjective t
  simp only [P, Category.assoc, dgModuleCoproductHomologyIso_ι_inv_assoc]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
  have hcol : Sigma.ι (dgCoherentBarLayerFamily R D G 0)
        (dgCoherentBarLayerIndexEquiv (nerve J) 0 s) ≫
      (dgBarZeroLayerInclusion R D G ≫ dgCoherentBarCoconeUniversalMap R D G
        (dgCoherentBarMaurerCartan_unconditional R D G) c) =
      (moduleShiftZeroIsoObj R D (dgCoherentBarSource R D G ⟨0, s.val⟩)).hom ≫
        dgBarCoconeVertexModuleMap R D G c s.val := by
    change Sigma.ι (dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s.val) ≫ _ = _
    rw [← Category.assoc, dgBarZeroLayerInclusion_ι, Category.assoc]
    rfl
  rw [hcol, Functor.map_comp, HomologicalComplex.homologyMap_comp]
  have hi := dgCoherentBarNaturalLayerHomologyIso_ι R D G x 0 q q (by omega) s
  erw [hi]
  simp only [Category.assoc]
  rw [dgHomologyBarNondegAugmentation_ι, dgCoherentCoconeHomology_source_leg]
  erw [dgBarZeroShiftHomology]

lemma dgBarCoconeUniversal_homology (c : JoinCocone G) (x : D) (q : ℤ) :
    dgCoherentBarHomologyBarAugmentation R D G x q ≫
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (dgCoherentBarCoconeUniversalMap R D G (dgCoherentBarMaurerCartan_unconditional R D G) c)) q =
    dgHomologyBarNondegAugmentation R (dgCoherentBarHomologyDiagram R D G x q)
      (dgCoherentCoconeHomology R D G c x q) := by
  rw [← cancel_epi (dgCoherentBarNaturalLayerHomologyIso R D G x 0 q q (by omega)).hom]
  rw [← Category.assoc, ← dgBarZeroLayerInclusion_homology,
    ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
    dgBarCoconeUniversal_zeroLayer_homology]

lemma dgBarCoconeUniversal_quasiIso_of_homologyColimit (c : JoinCocone G)
    (hc : ∀ x q, IsColimit (dgCoherentCoconeHomology R D G c x q)) :
    moduleQuasiIso R D (dgCoherentBarCoconeUniversalMap R D G
      (dgCoherentBarMaurerCartan_unconditional R D G) c) := by
  apply dgCoherentBarMap_quasiIso R D G _
    (dgCoherentCoconeHomology R D G c) hc (fun _ _ => rfl)
  intro x q
  simpa only [eqToHom_refl, Category.comp_id] using!
    dgBarCoconeUniversal_homology R D G c x q

end SerrePositivity.InfinityCategories
