module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyCocone
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegAugmentationLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictZeroLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroStageAugmentation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyBarCofork

/-!
概要：零次元層の strict 増大は、自然な層同型を通して H(G) bar の標準増大になる。
方針：各実直和包含で、零 shift 同型と元の余極限の脚を比較する。
規約：元の strict 標準射と同じ脚を使う。
使われ方：strict 標準増大のホモロジー射が余核比較同型であることの証明。
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
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)

set_option maxHeartbeats 800000 in
-- The coproduct/reindex comparison unfolds several selected homology objects.
lemma dgCoherentBarStrictZeroLayer_homologyAugmentation (x : D) (q : ℤ) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (dgCoherentBarLayerInclusion R D (dgCoherentBarStrictDiagram R D F) 0 ≫
        dgCoherentBarStrictAugmentationGraded R D F (colimit.cocone F))) q =
    (dgCoherentBarNaturalLayerHomologyIso R D (dgCoherentBarStrictDiagram R D F)
      x 0 q q (by omega)).hom ≫
      dgHomologyBarNondegAugmentation R
        (dgCoherentBarHomologyDiagram R D (dgCoherentBarStrictDiagram R D F) x q)
        (dgStrictCoherentHomologyCocone R D F x q) := by
  let G := dgCoherentBarStrictDiagram R D F
  let P := dgModuleCoproductHomologyIso R D (dgCoherentBarLayerFamily R D G 0) x q
  rw [← cancel_epi P.inv]
  apply Sigma.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (dgCoherentBarLayerIndexEquiv (nerve J) 0).surjective t
  simp only [P, Category.assoc, dgModuleCoproductHomologyIso_ι_inv_assoc]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← CategoryTheory.Functor.map_comp]
  have hcol : Sigma.ι (dgCoherentBarLayerFamily R D G 0)
      (dgCoherentBarLayerIndexEquiv (nerve J) 0 s) ≫
      (dgCoherentBarLayerInclusion R D G 0 ≫
        dgCoherentBarStrictAugmentationGraded R D F (colimit.cocone F)) =
    (moduleShiftZeroIsoObj R D (ForgetEnrichment.to (Complex R)
      (F.obj (s.val.obj 0)))).hom ≫ colimit.ι F (s.val.obj 0) := by
    rw [dgCoherentBarLayerInclusion_ι_assoc, dgCoherentBarStrictAugmentationGraded_ι]
    rfl
  rw [hcol, CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp]
  have hi := dgCoherentBarNaturalLayerHomologyIso_ι R D G x 0 q q (by omega) s
  erw [hi]
  simp only [Category.assoc]
  rw [dgHomologyBarNondegAugmentation_ι]
  rw [dgStrictCoherentHomologyCocone_leg R D F x q]
  rw [dgCoherentBarStrictSourceHomologyIso R D F x q 0 s.val]
  rw [Iso.inv_hom_id_assoc]
  erw [dgBarZeroShiftHomology R D (ForgetEnrichment.to (Complex R)
    (F.obj (s.val.obj 0))) x q]

end SerrePositivity.InfinityCategories
