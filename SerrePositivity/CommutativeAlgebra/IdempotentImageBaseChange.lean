module
public import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator

/-! # Transport of quotient-image idempotence to coefficient algebras -/
@[expose] public section
universe u v
namespace SerrePositivity
variable {S : Type u} {C : Type v} [CommRing S] [CommRing C]

/-- Mapping an ideal preserves its idempotence, without a surjectivity assumption. -/
lemma ideal_map_isIdempotent (φ : S →+* C) (I : Ideal S) (hI : IsIdempotentElem I) :
    IsIdempotentElem (I.map φ) := by
  change I * I = I at hI
  change I.map φ * I.map φ = I.map φ
  rw [← Ideal.map_mul, hI]

/-- Quotient-image idempotence transports along any compatible quotient map. -/
lemma quotient_image_idempotent_baseChange (φ : S →+* C) (I J : Ideal S) (K : Ideal C)
    (hJK : J ≤ K.comap φ)
    (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk J))) :
    IsIdempotentElem ((I.map φ).map (Ideal.Quotient.mk K)) := by
  let ψ := Ideal.quotientMap (I := J) K φ hJK
  have h := ideal_map_isIdempotent ψ (I.map (Ideal.Quotient.mk J)) hI
  have heq : (I.map φ).map (Ideal.Quotient.mk K) =
      (I.map (Ideal.Quotient.mk J)).map ψ := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  rw [heq]
  exact h

/-- In particular, images modulo corresponding scalar powers remain idempotent. -/
lemma quotient_power_image_idempotent_baseChange (φ : S →+* C) (I : Ideal S) (a : S) (n : ℕ)
    (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n})))) :
    IsIdempotentElem ((I.map φ).map (Ideal.Quotient.mk (Ideal.span {φ a ^ n}))) := by
  apply quotient_image_idempotent_baseChange φ I (Ideal.span {a ^ n}) _ _ hI
  rw [Ideal.span_singleton_le_iff_mem]
  change φ (a ^ n) ∈ Ideal.span {φ a ^ n}
  rw [map_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The entire positive-power family of idempotence hypotheses transports unchanged. -/
lemma quotient_power_images_idempotent_baseChange (φ : S →+* C) (I : Ideal S) (a : S)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n})))) :
    ∀ n : ℕ, 0 < n →
      IsIdempotentElem ((I.map φ).map (Ideal.Quotient.mk (Ideal.span {φ a ^ n}))) :=
  fun n hn => quotient_power_image_idempotent_baseChange φ I a n (hI n hn)

end SerrePositivity
