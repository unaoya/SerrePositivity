module

public import SerrePositivity.BhattScholze.OrientedPrismHom

/-! # 完全oriented prism射の生成元と商同型

著者公開版Lemma 3.5の主イデアルの射について、生成元の像の一意な単元係数を
構成する。台の環射が同型なら標準商も同型となる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 完全oriented prism射は、源の生成元を終域の生成元の一意な単元倍へ送る。 -/
theorem existsUnique_generator_unit (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    ∃! u : Bˣ, f.toRingHom P.generator = Q.generator * u := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp f.map_generator_mem
  have hdist := f.map_delta.map_isDistinguished (P.isDistinguished_of_perfect hP)
  rw [hr] at hdist
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_perfect hQ
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

/-- 台環射が全単射の完全oriented prism射は、具体的な標準商同型を与える。 -/
def quotientEquiv (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    A ⧸ P.ideal ≃+* B ⧸ Q.ideal :=
  Ideal.quotientEquiv P.ideal Q.ideal (RingEquiv.ofBijective f.toRingHom hf)
    (f.map_ideal_eq_of_perfect hP hQ).symm

/-- 構成した商同型は既存の誘導商射に一致する。 -/
@[simp] theorem quotientEquiv_toRingHom (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    (f.quotientEquiv hP hQ hf).toRingHom = f.quotientMap := rfl

/-- 完全oriented prismの同型は商上でも全単射。 -/
theorem quotientMap_bijective (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    Function.Bijective f.quotientMap := (f.quotientEquiv hP hQ hf).bijective

end SerrePositivity.BhattScholze.OrientedPrism.Hom
