module

public import SerrePositivity.PerfectComplex.ClosedSupportRelations

/-! # Perfectness of degreewise retracts

The retraction need not be a chain map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

lemma strictlyPerfectComplex_of_degreewiseRetract
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (i : K ⟶ L)
    (r : ∀ n, L.X n ⟶ K.X n) (hr : ∀ n, i.f n ≫ r n = 𝟙 (K.X n))
    (hL : strictlyPerfectComplex R L) : strictlyPerfectComplex R K := by
  have hz : ∀ n, IsZero (L.X n) → IsZero (K.X n) := by
    intro n hn
    rw [IsZero.iff_id_eq_zero, ← hr n, hn.eq_of_tgt (i.f n) 0, zero_comp]
  obtain ⟨a, b, ha, hb⟩ := hL.1
  refine ⟨⟨a, b, ?_, ?_⟩, fun n => ?_⟩
  · exact (K.isStrictlyGE_iff a).mpr fun n hn => hz n (L.isZero_of_isStrictlyGE a n hn)
  · exact (K.isStrictlyLE_iff b).mpr fun n hn => hz n (L.isZero_of_isStrictlyLE b n hn)
  · have := (hL.2 n).1
    have := (hL.2 n).2
    have hs : Function.Surjective (r n).hom := by
      intro x
      exact ⟨(i.f n).hom x, congrArg (fun f => f.hom x) (hr n)⟩
    exact ⟨Module.Finite.of_surjective (r n).hom hs,
      Module.Projective.of_split (i.f n).hom (r n).hom (congrArg (fun f => f.hom) (hr n))⟩

end SerrePositivity
