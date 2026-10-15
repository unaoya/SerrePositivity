module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Quillen.FullyFaithfulReflection

/-! # Universe lift between specified simplicial model structures

The models are explicit, with the mono/Kan classes in each universe.
Universe lift preserves and reflects the two right classes, preserves
cofibrations, reflects all weak equivalences, and preserves weak
equivalences between fibrant objects. No adjoint is asserted.
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

include hfib hfib' in
lemma fibrations_map_iff {X Y : SSet.{v}} (p : X ⟶ Y) :
    fibrations SSet.{max v w} (SSet.uliftFunctor.{w, v}.map p) ↔ fibrations SSet.{v} p := by
  rw [hfib, hfib']
  exact horn_rightClass_iff p

include hcof hcof' in
lemma trivialFibrations_map_iff {X Y : SSet.{v}} (p : X ⟶ Y) :
    trivialFibrations SSet.{max v w} (SSet.uliftFunctor.{w, v}.map p) ↔
      trivialFibrations SSet.{v} p := by
  rw [← cofibrations_rlp SSet.{max v w}, ← cofibrations_rlp SSet.{v}, hcof, hcof',
    SSet.rlp_monomorphisms, SSet.rlp_monomorphisms]
  exact boundary_rightClass_iff p

include hcof hfib hcof' hfib' in
lemma isRightQuillen : Quillen.IsRightQuillen SSet.uliftFunctor.{w, v} where
  map_fibrations _ _ p hp := (fibrations_map_iff.{w, v} hfib hfib' p).mpr hp
  map_trivialFibrations _ _ p hp := (trivialFibrations_map_iff.{w, v} hcof hcof' p).mpr hp

include hcof hcof' in
lemma cofibrations_map :
    cofibrations SSet.{v} ≤
      (cofibrations SSet.{max v w}).inverseImage SSet.uliftFunctor.{w, v} := by
  intro X Y f hf
  have : Mono f := by rw [hcof] at hf; exact hf
  change cofibrations SSet.{max v w} (SSet.uliftFunctor.{w, v}.map f)
  rw [hcof']
  exact mono_map f

include hcof hfib hcof' hfib' in
lemma weakEquivalence_of_map {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : weakEquivalences SSet.{max v w} (SSet.uliftFunctor.{w, v}.map f)) :
    weakEquivalences SSet.{v} f := by
  have := isRightQuillen.{w, v} hcof hfib hcof' hfib'
  exact Quillen.weakEquivalence_of_map SSet.uliftFunctor.{w, v}
    (cofibrations_map.{w, v} hcof hcof') f hf

include hcof hfib hcof' hfib' in
lemma weakEquivalences_map_iff_of_fibrant {X Y : SSet.{v}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) :
    weakEquivalences SSet.{max v w} (SSet.uliftFunctor.{w, v}.map f) ↔
      weakEquivalences SSet.{v} f := by
  constructor
  · exact weakEquivalence_of_map.{w, v} hcof hfib hcof' hfib' f
  · intro hf
    have := isRightQuillen.{w, v} hcof hfib hcof' hfib'
    have : WeakEquivalence f := ⟨hf⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_fibrant _ f)

end SerrePositivity.SimplicialModel.UniverseLift
