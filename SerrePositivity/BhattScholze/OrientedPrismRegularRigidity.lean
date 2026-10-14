module

public import SerrePositivity.BhattScholze.OrientedPrismHom

/-! # p正則なoriented prism射の剛性

著者公開版Lemma 3.5の主イデアルの局所計算。
完全性を要求せず、pの正則性とprismの実導来完備性から古典的p完備性を得て使う。
pねじれのある一般prismやCartierイデアルの降下はこの定理の範囲外。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- p正則なoriented prism射は、生成元を一意な単元係数で写す。 -/
theorem existsUnique_generator_unit_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    ∃! u : Bˣ, f.toRingHom P.generator = Q.generator * u := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp f.map_generator_mem
  have hdist := f.map_delta.map_isDistinguished (P.isDistinguished_of_p_regular hP)
  rw [hr] at hdist
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_regular hQ
  have hru : IsUnit r :=
    (Q.deltaStructure.isDistinguished_factor Q.generator r hdist
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator})
        (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B)})
        (Ideal.subset_span (by simp)))).2
  obtain ⟨u, hu⟩ := hru
  refine ⟨u, by simpa only [hu] using hr, ?_⟩
  intro v hv
  apply Units.ext
  apply Q.generator_regular
  change Q.generator * (v : B) = Q.generator * (u : B)
  exact hv.symm.trans (by simpa only [hu] using hr)

/-- p正則なoriented prism射のイデアル像は終域のprismイデアル全体。 -/
theorem map_ideal_eq_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) : P.ideal.map f.toRingHom = Q.ideal := by
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_regular hQ
  exact f.map_delta.map_span_eq_of_distinguished_of_mem_span
    (P.isDistinguished_of_p_regular hP) f.map_generator_mem
    (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B)}) (Ideal.subset_span (by simp)))

/-- p正則なoriented prism射の生成元像は非零因子。 -/
theorem map_generator_mul_injective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    Function.Injective (fun x : B ↦ f.toRingHom P.generator * x) := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit_of_p_regular hP hQ
  intro x y hxy
  change f.toRingHom P.generator * x = f.toRingHom P.generator * y at hxy
  rw [hu, mul_assoc, mul_assoc] at hxy
  have h := Q.generator_regular hxy
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp u.isUnit).1 h

end SerrePositivity.BhattScholze.OrientedPrism.Hom
