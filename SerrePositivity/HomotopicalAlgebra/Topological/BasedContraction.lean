module

public import SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence

/-! # Based contractions and the actual homotopy maps

A contraction fixing its basepoint contracts every cubical loop relative
to the entire boundary. Thus all homotopy classes at that point coincide.
No model structure or assertion about unbased homotopies is used.
-/

@[expose] public section
universe u v w
noncomputable section
open CategoryTheory

namespace SerrePositivity.TopologicalHomotopy
variable {X : Type u} [TopologicalSpace X]

abbrev BasedContraction (x : X) :=
  ContinuousMap.HomotopyRel (ContinuousMap.id X) (ContinuousMap.const X x) {x}

def BasedContraction.ofHomeomorph {Y : Type v} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (H : BasedContraction (e x)) : BasedContraction x where
  toHomotopy :=
    { toFun z := e.symm (H (z.1, e z.2))
      continuous_toFun := e.symm.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
      map_zero_left z := by
        change e.symm (H (0, e z)) = z
        rw [H.apply_zero]
        exact e.symm_apply_apply z
      map_one_left z := by
        change e.symm (H (1, e z)) = x
        rw [H.apply_one]
        exact e.symm_apply_apply x }
  prop' t z hz := by
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    change e.symm (H (t, e x)) = x
    rw [H.eq_fst t (Set.mem_singleton _)]
    exact e.symm_apply_apply x

lemma loop_homotopic_const {N : Type w} {x : X} (H : BasedContraction x) (p : GenLoop N X x) :
    GenLoop.Homotopic p GenLoop.const := by
  refine ⟨{
    toHomotopy := {
      toFun := fun z ↦ H (z.1, p z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk (p.1.continuous.comp continuous_snd))
      map_zero_left := fun z ↦ H.apply_zero (p z)
      map_one_left := fun z ↦ H.apply_one (p z) }
    prop' := ?_ }⟩
  intro t z hz
  change H (t, p z) = p z
  have hp : p z = x := p.property z hz
  exact (congrArg (fun a ↦ H (t, a)) hp).trans ((H.eq_fst t (Set.mem_singleton _)).trans hp.symm)

lemma homotopyGroup_subsingleton {N : Type w} {x : X} (H : BasedContraction x) :
    Subsingleton (HomotopyGroup N X x) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with | _ p =>
  induction b using Quotient.inductionOn with | _ q =>
  exact (Quotient.sound (loop_homotopic_const H p)).trans
    (Quotient.sound (loop_homotopic_const H q)).symm

lemma weakHomotopyEquivalences_of_basedContractions {A B : TopCat.{u}}
    [PathConnectedSpace A] [PathConnectedSpace B]
    (hA : ∀ x : A, Nonempty (BasedContraction x))
    (hB : ∀ x : B, Nonempty (BasedContraction x)) (f : A ⟶ B) :
    weakHomotopyEquivalences f := by
  constructor
  · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
      fun _ ↦ ⟨ZerothHomotopy.mk (Classical.arbitrary A), Subsingleton.elim _ _⟩⟩
  · intro x n
    have := homotopyGroup_subsingleton (N := Fin (n + 1)) (Classical.choice (hA x))
    have := homotopyGroup_subsingleton (N := Fin (n + 1)) (Classical.choice (hB (f x)))
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩

end SerrePositivity.TopologicalHomotopy
