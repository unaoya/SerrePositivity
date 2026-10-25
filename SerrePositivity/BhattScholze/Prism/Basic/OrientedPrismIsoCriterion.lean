module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHomRigidity
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # oriented prismの商による同型判定

著者公開版Theorem 3.10の最後のd進完備な環の比較に使う。
既存の完備性による全射判定を使い、核の元の反復除算とd進分離性で単射性を証明する。
p正則なprismへの適用も公開する。perfectoid/prism比較射の存在はこの定理の対象外。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 完全oriented prism射の生成元の像は非零因子。 -/
theorem map_generator_mul_injective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Injective (fun x : B ↦ f.toRingHom P.generator * x) :=
  f.map_generator_mul_injective_of_p_regular hP.p_mul_injective hQ.p_mul_injective

/-- 商射が単射なら台環射も単射。
核の元を生成元で繰り返し割り、d進分離性で零と判定する。 -/
theorem injective_of_quotientMap_injective_of_generator_regular (f : Hom P Q)
    (hgen : Function.Injective (fun x : B ↦ f.toRingHom P.generator * x))
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom := by
  have hfirst (x : A) (hx : f.toRingHom x = 0) : x ∈ P.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hf
    rw [f.quotientMap_mk, hx, map_zero, map_zero]
  have hpow (n : ℕ) (x : A) (hx : f.toRingHom x = 0) : x ∈ P.ideal ^ n := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (hfirst x hx)
      have hyker : f.toRingHom y = 0 := by
        apply hgen
        change f.toRingHom P.generator * f.toRingHom y = f.toRingHom P.generator * 0
        rw [mul_zero, ← map_mul, ← hy, hx]
      rw [hy, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih y hyker)
  apply (injective_iff_map_eq_zero f.toRingHom).mpr
  intro x hx
  let : IsAdicComplete P.ideal A := P.isAdicComplete_generator
  apply IsHausdorff.haus' (I := P.ideal) x
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero, smul_eq_mul, Ideal.mul_top] using hpow n x hx

/-- 完全prismの商射が単射なら台環射も単射。既存公開入口を保持する。 -/
theorem injective_of_quotientMap_injective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom :=
  f.injective_of_quotientMap_injective_of_generator_regular
    (f.map_generator_mul_injective hP hQ) hf

/-- p正則なoriented prismの商射が単射なら、台環射も単射。 -/
theorem injective_of_quotientMap_injective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x))
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom :=
  f.injective_of_quotientMap_injective_of_generator_regular
    (f.map_generator_mul_injective_of_p_regular hP hQ) hf

/-- 商射が全射なら台環射も全射。
既存の主イデアル進完備性による全射判定にイデアル像の一致を供給する。 -/
theorem surjective_of_quotientMap_surjective_of_map_ideal_eq (f : Hom P Q)
    (heq : P.ideal.map f.toRingHom = Q.ideal)
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom := by
  let : IsAdicComplete P.ideal A := P.isAdicComplete_generator
  let : IsAdicComplete Q.ideal B := Q.isAdicComplete_generator
  let : IsHausdorff (P.ideal.map f.toRingHom) B := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := P.ideal) f.toRingHom
  rw [heq, ← f.quotientMap_comp_mk]
  exact hf.comp Ideal.Quotient.mk_surjective

/-- 完全prismの商射が全射なら台環射も全射。既存公開入口を保持する。 -/
theorem surjective_of_quotientMap_surjective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom :=
  f.surjective_of_quotientMap_surjective_of_map_ideal_eq (f.map_ideal_eq_of_perfect hP hQ) hf

/-- p正則なoriented prismの商射が全射なら、台環射も全射。 -/
theorem surjective_of_quotientMap_surjective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x))
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom :=
  f.surjective_of_quotientMap_surjective_of_map_ideal_eq (f.map_ideal_eq_of_p_regular hP hQ) hf

/-- p正則なoriented prism射は、標準商射が全単射であることと同値に全単射。
完全性を仮定せず、p正則性と実導来完備性の共通比較を使う。 -/
theorem bijective_iff_quotientMap_bijective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    Function.Bijective f.toRingHom ↔ Function.Bijective f.quotientMap := by
  constructor
  · intro hf
    exact (Ideal.quotientEquiv P.ideal Q.ideal (RingEquiv.ofBijective f.toRingHom hf)
      (f.map_ideal_eq_of_p_regular hP hQ).symm).bijective
  · intro hf
    exact ⟨f.injective_of_quotientMap_injective_of_p_regular hP hQ hf.1,
      f.surjective_of_quotientMap_surjective_of_p_regular hP hQ hf.2⟩

/-- 完全oriented prism射は、標準商射が全単射であることと同値に全単射。 -/
theorem bijective_iff_quotientMap_bijective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Bijective f.toRingHom ↔ Function.Bijective f.quotientMap := by
  constructor
  · exact f.quotientMap_bijective hP hQ
  · intro h
    exact ⟨f.injective_of_quotientMap_injective hP hQ h.1,
      f.surjective_of_quotientMap_surjective hP hQ h.2⟩

/-- 完全oriented prismの標準商上の全単射から構成する台環の同型。 -/
def ringEquivOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) : A ≃+* B :=
  RingEquiv.ofBijective f.toRingHom ((f.bijective_iff_quotientMap_bijective hP hQ).mpr hf)

/-- 構成した台環同型は元のprism射を台環射として持つ。 -/
@[simp] theorem ringEquivOfQuotient_toRingHom (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    (f.ringEquivOfQuotient hP hQ hf).toRingHom = f.toRingHom := rfl

/-- 商上の全単射から構成した台環同型の逆は、再びprism射となる。 -/
def inverseOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) : Hom Q P := by
  let e := f.ringEquivOfQuotient hP hQ hf
  refine ⟨e.symm.toRingHom, ?_, ?_⟩
  · apply DeltaStructure.IsDeltaHom.symm (e := e)
    exact f.map_delta
  · intro y hy
    rw [← f.map_ideal_eq_of_perfect hP hQ] at hy
    obtain ⟨x, hx, hxy⟩ := Ideal.mem_image_of_mem_map_of_surjective f.toRingHom
      ((f.bijective_iff_quotientMap_bijective hP hQ).mpr hf).2 hy
    change e.symm y ∈ P.ideal
    rw [← hxy]
    change e.symm (e x) ∈ P.ideal
    rw [RingEquiv.symm_apply_apply]
    exact hx

/-- 構成した逆prism射との合成は源の恒等prism射。 -/
@[simp] theorem inverseOfQuotient_comp (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    (f.inverseOfQuotient hP hQ hf).comp f = Hom.id P := by
  apply Hom.ext
  apply RingHom.ext
  intro x
  change (f.ringEquivOfQuotient hP hQ hf).symm ((f.ringEquivOfQuotient hP hQ hf) x) = x
  exact RingEquiv.symm_apply_apply _ x

/-- 逆prism射との逆順の合成は終域の恒等prism射。 -/
@[simp] theorem comp_inverseOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    f.comp (f.inverseOfQuotient hP hQ hf) = Hom.id Q := by
  apply Hom.ext
  apply RingHom.ext
  intro x
  change (f.ringEquivOfQuotient hP hQ hf) ((f.ringEquivOfQuotient hP hQ hf).symm x) = x
  exact RingEquiv.apply_symm_apply _ x

end SerrePositivity.BhattScholze.OrientedPrism.Hom
