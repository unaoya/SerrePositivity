module
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftModel
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap

/-! # Simplicial universe lift preserves and reflects all weak equivalences

The image of each horn generator is compared by an actual arrow isomorphism.
Colimit preservation transports relative horn cells and their retracts.
Brown's lemma applies to every simplicial set, since all are cofibrant.
-/

@[expose] public section
universe w v
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.UniverseLift
variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcof' : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfib' : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

omit [ModelCategory SSet.{v}] in
include hfib' in
lemma hornGenerators_map : SSet.modelCategoryQuillen.J.{v} ≤
    (trivialCofibrations SSet.{max v w}).inverseImage SSet.uliftFunctor.{w, v} := by
  intro A B f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  have h : trivialCofibrations SSet.{max v w} (SSet.horn (n + 1) i).ι := by
    rw [← fibrations_llp, hfib']
    exact SSet.modelCategoryQuillen.J.le_llp_rlp _
      (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) i)
  exact ((trivialCofibrations SSet.{max v w}).arrow_mk_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornArrowIso (n + 1) i)).mpr h

include hfib hfib' in
lemma trivialCofibrations_map : trivialCofibrations SSet.{v} ≤
    (trivialCofibrations SSet.{max v w}).inverseImage SSet.uliftFunctor.{w, v} := by
  have hcells : Quillen.relativeCells.{v} (trivialCofibrations SSet.{max v w}) ≤
      trivialCofibrations SSet.{max v w} := by
    rw [← fibrations_llp]
    exact (MorphismProperty.transfiniteCompositions_monotone
      ((MorphismProperty.pushouts_monotone (fibrations SSet.{max v w}).llp.coproducts_le).trans
        (fibrations SSet.{max v w}).llp.pushouts_le)).trans
      (fibrations SSet.{max v w}).llp.transfiniteCompositions_le
  have hsource : trivialCofibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp.llp := by
    rw [← hfib, fibrations_llp]
  rw [hsource]
  apply ModelGeneration.generatedLeft_le_of_cells_le
  intro X Y f hf
  exact hcells _ (ModelGeneration.relativeCells_map_le SSet.uliftFunctor.{w, v}
    SSet.modelCategoryQuillen.J (trivialCofibrations SSet.{max v w})
    (hornGenerators_map.{w, v} hfib') f hf)

include hcof hfib hcof' hfib' in
lemma isLeftQuillen : Quillen.IsLeftQuillen SSet.uliftFunctor.{w, v} where
  map_cofibrations := cofibrations_map.{w, v} hcof hcof'
  map_trivialCofibrations := trivialCofibrations_map.{w, v} hfib hfib'

include hcof hfib hcof' hfib' in
lemma weakEquivalences_map_iff {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{max v w} (SSet.uliftFunctor.{w, v}.map f) ↔
      weakEquivalences SSet.{v} f := by
  constructor
  · exact weakEquivalence_of_map.{w, v} hcof hfib hcof' hfib' f
  · intro hf
    have := isLeftQuillen.{w, v} hcof hfib hcof' hfib'
    have : IsCofibrant X := by constructor; rw [hcof]; exact inferInstanceAs (Mono _)
    have : IsCofibrant Y := by constructor; rw [hcof]; exact inferInstanceAs (Mono _)
    have : WeakEquivalence f := ⟨hf⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant _ f)

include hcof hfib hcof' hfib' in
/-- Independent universes may be compared in their common maximum universe. -/
lemma weakEquivalences_iff_of_liftedArrowIso [ModelCategory SSet.{w}]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    {X Y : SSet.{v}} (f : X ⟶ Y) {X' Y' : SSet.{w}} (g : X' ⟶ Y')
    (e : Arrow.mk (SSet.uliftFunctor.{w, v}.map f) ≅
      Arrow.mk (SSet.uliftFunctor.{v, w}.map g)) :
    weakEquivalences SSet.{v} f ↔ weakEquivalences SSet.{w} g :=
  (weakEquivalences_map_iff.{w, v} hcof hfib hcof' hfib' f).symm.trans
    (((weakEquivalences SSet.{max v w}).arrow_mk_iso_iff e).trans
      (weakEquivalences_map_iff.{v, w} hcofW hfibW hcof' hfib' g))

end SerrePositivity.SimplicialModel.UniverseLift
