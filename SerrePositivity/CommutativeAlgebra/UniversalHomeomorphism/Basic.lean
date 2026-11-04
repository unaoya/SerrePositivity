module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# 可換環の射の普遍同相

## 概要
整性と Spec の全射性、単射性、剰余体拡大の純非分離性で普遍同相を表す。

## 方針
標数 p では核が nil であり、各元の適当な p 冪が像に入ることで判定する。

## 規約
核の条件は `RingHom.ker f ≤ nilradical A`。冪零指数は元ごとに取る。

## 使われ方
有限エタール層別の各層の後半の射を記述する（BS Lemma 10.12）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 概要：G-A8-4：環の射が普遍同相：整・Spec で全射・radicial（普遍単射：剰余体の拡大が純非分離で Spec で単射）。
方針：定義。
規約：—
使われ方：Lemma 10.12 (2)。 -/
structure IsUniversalHomeomorphism {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop where
  isIntegral : f.IsIntegral
  surjective_spec : Function.Surjective (PrimeSpectrum.comap f)
  radicial : Function.Injective (PrimeSpectrum.comap f) ∧
    ∀ Q : PrimeSpectrum B,
      let P := (PrimeSpectrum.comap f Q).asIdeal
      letI := (Ideal.ResidueField.map P Q.asIdeal f rfl).toAlgebra
      IsPurelyInseparable P.ResidueField Q.asIdeal.ResidueField

/-- 全射な体の射は純非分離。剰余体の同型を運ぶ際に用いる。 -/
private theorem purelyInseparable_of_surjective {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Surjective f) : f.IsPurelyInseparable := by
  let := f.toAlgebra
  exact ⟨⟨f.isIntegral_of_surjective hf⟩, fun x _ ↦ hf x⟩

set_option backward.isDefEq.respectTransparency false in
/-- 標準の剰余体の射は環準同型の合成と両立する。 -/
private theorem residueFieldMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (Q : PrimeSpectrum C) :
    (Ideal.ResidueField.map (PrimeSpectrum.comap g Q).asIdeal Q.asIdeal g rfl).comp
        (Ideal.ResidueField.map (PrimeSpectrum.comap (g.comp f) Q).asIdeal
          (PrimeSpectrum.comap g Q).asIdeal f rfl) =
      Ideal.ResidueField.map (PrimeSpectrum.comap (g.comp f) Q).asIdeal Q.asIdeal
        (g.comp f) rfl := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]

section SpecComparison

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Spec の剰余体同型は環から定義した剰余体写像と両立する。 -/
private theorem spec_residueFieldMap_compat {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Q : PrimeSpectrum B) :
    (Scheme.Spec.residueFieldIso (.of A) (PrimeSpectrum.comap f Q)).inv ≫
        (Spec.map (CommRingCat.ofHom f)).residueFieldMap Q ≫
        (Scheme.Spec.residueFieldIso (.of B) Q).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (PrimeSpectrum.comap f Q).asIdeal
        Q.asIdeal f rfl) := by
  apply CommRingCat.hom_ext
  apply Ideal.ResidueField.ringHom_ext
  change (CommRingCat.ofHom (algebraMap A _) ≫ _).hom =
    (CommRingCat.ofHom (algebraMap A _) ≫ _).hom
  apply congrArg CommRingCat.Hom.hom
  have hn : CommRingCat.ofHom (algebraMap A (PrimeSpectrum.comap f Q).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (PrimeSpectrum.comap f Q).asIdeal
        Q.asIdeal f rfl) =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap B Q.asIdeal.ResidueField) := by
    ext a
    exact Ideal.ResidueField.map_algebraMap _ _ _ _ a
  rw [hn, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc]
  change (Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).Γevaluation _ ≫
      (Spec.map (CommRingCat.ofHom f)).residueFieldMap Q ≫ _ = _
  rw [Scheme.Γevaluation_naturality_assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- 剰余体の二つのモデルの純非分離性は同値。 -/
private theorem spec_residueFieldMap_isPurelyInseparable_iff
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (Q : PrimeSpectrum B) :
    ((Spec.map (CommRingCat.ofHom f)).residueFieldMap Q).hom.IsPurelyInseparable ↔
      (Ideal.ResidueField.map (PrimeSpectrum.comap f Q).asIdeal Q.asIdeal f rfl).IsPurelyInseparable := by
  let eA := Scheme.Spec.residueFieldIso (.of A) (PrimeSpectrum.comap f Q)
  let eB := Scheme.Spec.residueFieldIso (.of B) Q
  let r := (Spec.map (CommRingCat.ofHom f)).residueFieldMap Q
  have hA := purelyInseparable_of_surjective eA.inv.hom
    eA.symm.commRingCatIsoToRingEquiv.surjective
  have hB := purelyInseparable_of_surjective eB.hom.hom
    eB.commRingCatIsoToRingEquiv.surjective
  have hAi := purelyInseparable_of_surjective eA.hom.hom
    eA.commRingCatIsoToRingEquiv.surjective
  have hBi := purelyInseparable_of_surjective eB.inv.hom
    eB.symm.commRingCatIsoToRingEquiv.surjective
  constructor
  · intro h
    have ht := (hA.comp h).comp hB
    change (eA.inv ≫ r ≫ eB.hom).hom.IsPurelyInseparable at ht
    rw [spec_residueFieldMap_compat] at ht
    exact ht
  · intro h
    rw [← spec_residueFieldMap_compat f Q] at h
    have ht := (hAi.comp h).comp hBi
    change (eA.hom ≫ (eA.inv ≫ r ≫ eB.hom) ≫ eB.inv).hom.IsPurelyInseparable at ht
    simpa using ht

/-- 環の定義と Spec の普遍単射性を接続する。 -/
private theorem radicial_iff_universallyInjective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (Function.Injective (PrimeSpectrum.comap f) ∧ ∀ Q : PrimeSpectrum B,
      (Ideal.ResidueField.map (PrimeSpectrum.comap f Q).asIdeal Q.asIdeal f rfl).IsPurelyInseparable) ↔
      UniversallyInjective (Spec.map (CommRingCat.ofHom f)) := by
  rw [(tfae_universallyInjective (Spec.map (CommRingCat.ofHom f))).out 0 2]
  exact and_congr Iff.rfl (forall_congr' fun Q ↦
    (spec_residueFieldMap_isPurelyInseparable_iff f Q).symm)

end SpecComparison

/-- 概要：普遍同相は底変換・合成で安定、nil イデアルによる商は普遍同相。 -/
theorem isUniversalHomeomorphism_baseChange {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) (hf : IsUniversalHomeomorphism f) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    IsUniversalHomeomorphism (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom := by
  let : Algebra A B := f.toAlgebra
  let : Algebra A C := g.toAlgebra
  let i := (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
  have hpb := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A B C)
  have hi : AlgebraicGeometry.IsIntegralHom
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) :=
    AlgebraicGeometry.IsIntegralHom.SpecMap_iff.mpr hf.isIntegral
  have hs : AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := ⟨hf.surjective_spec⟩
  have hr := (radicial_iff_universallyInjective f).mp hf.radicial
  have hi' := CategoryTheory.MorphismProperty.of_isPullback
    (P := @AlgebraicGeometry.IsIntegralHom) hpb hi
  have hs' := CategoryTheory.MorphismProperty.of_isPullback
    (P := @AlgebraicGeometry.Surjective) hpb hs
  have hr' := CategoryTheory.MorphismProperty.of_isPullback
    (P := @AlgebraicGeometry.UniversallyInjective) hpb hr
  exact ⟨AlgebraicGeometry.IsIntegralHom.SpecMap_iff.mp hi', hs'.1,
    (radicial_iff_universallyInjective i).mpr hr'⟩

theorem isUniversalHomeomorphism_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : IsUniversalHomeomorphism f)
    (hg : IsUniversalHomeomorphism g) : IsUniversalHomeomorphism (g.comp f) := by
  refine ⟨hf.isIntegral.trans _ _ hg.isIntegral, hf.surjective_spec.comp hg.surjective_spec,
    hf.radicial.1.comp hg.radicial.1, ?_⟩
  intro Q
  have h := RingHom.IsPurelyInseparable.comp
    (hf.radicial.2 (PrimeSpectrum.comap g Q)) (hg.radicial.2 Q)
  rw [residueFieldMap_comp f g Q] at h
  exact h

theorem isUniversalHomeomorphism_of_nil_kernel {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical A) :
    IsUniversalHomeomorphism f := by
  have hs := PrimeSpectrum.isHomeomorph_comap f
    (fun x ↦ ⟨1, by omega, by simpa using hf x⟩) hker
  refine ⟨f.isIntegral_of_surjective hf, hs.surjective,
    hs.injective, ?_⟩
  intro Q
  exact purelyInseparable_of_surjective _
    ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective
      (PrimeSpectrum.comap f Q).asIdeal Q.asIdeal rfl).surjective

set_option backward.isDefEq.respectTransparency false in
/-- 元ごとの p 冪条件を剰余体の分数表示に移す。 -/
private theorem residueFieldMap_isPurelyInseparable_of_pow_mem
    {A B : Type*} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime]
    (hpA : (p : A) = 0) (f : A →+* B)
    (H : ∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range) (Q : PrimeSpectrum B) :
    (Ideal.ResidueField.map (PrimeSpectrum.comap f Q).asIdeal Q.asIdeal f rfl).IsPurelyInseparable := by
  let P := PrimeSpectrum.comap f Q
  let k := Ideal.ResidueField.map P.asIdeal Q.asIdeal f rfl
  let : CharP P.asIdeal.ResidueField p :=
    (charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (algebraMap A P.asIdeal.ResidueField), hpA, map_zero])
  let := k.toAlgebra
  apply (isPurelyInseparable_iff_pow_mem P.asIdeal.ResidueField p).mpr
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q.asIdeal) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change ∃ n, (algebraMap B Q.asIdeal.ResidueField a /
    algebraMap B Q.asIdeal.ResidueField b) ^ (p ^ n) ∈ k.range
  obtain ⟨n, c, hc⟩ := H a
  obtain ⟨m, d, hd⟩ := H b
  refine ⟨n + m, algebraMap A P.asIdeal.ResidueField (c ^ (p ^ m)) /
    algebraMap A P.asIdeal.ResidueField (d ^ (p ^ n)), ?_⟩
  simp only [map_div₀, k, Ideal.ResidueField.map_algebraMap, map_pow, hc, hd, div_pow]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_comm m n]

/-- 概要：標数 p の判定：F_p 代数の射が普遍同相 ⇔ 核の各元が冪零で、各 b の或る p^n 乗が像にある。 -/
theorem isUniversalHomeomorphism_iff_charP {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) (f : A →+* B) :
    IsUniversalHomeomorphism f ↔
      RingHom.ker f ≤ nilradical A ∧ ∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range := by
  constructor
  · intro hf
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mp
      hf.surjective_spec.denseRange, ?_⟩
    sorry -- 整かつ radicial な射から元ごとの p 冪条件を導く方向は有限部分代数に帰着して証明する
  · rintro ⟨hk, H⟩
    have hs := PrimeSpectrum.isHomeomorph_comap f
      (fun b ↦ by
        obtain ⟨n, hn⟩ := H b
        exact ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, hn⟩) hk
    refine ⟨?_, hs.surjective, hs.injective,
      residueFieldMap_isPurelyInseparable_of_pow_mem p hpA f H⟩
    let := f.toAlgebra
    intro b
    obtain ⟨n, a, ha⟩ := H b
    exact IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n)
      (ha ▸ f.isIntegralElem_map (x := a))

/-- 概要：G-A8-5：完全 F_p 環 A から被約環 B への普遍同相は同型。
方針：b^{p^n} = f(a)、a = σ^{p^n}、(b − f σ)^{p^n} = 0、B 被約 ⇒ b = f σ；核は nil で A 被約 ⇒ 零。
規約：`PerfectRing A p`。
使われ方：Thm 10.11 の n = 1 と 5。 -/
theorem isUniversalHomeomorphism_bijective_of_perfect_reduced
    {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) [PerfectRing A p] [IsReduced B]
    (f : A →+* B) (hf : IsUniversalHomeomorphism f) : Function.Bijective f := by
  obtain ⟨hk, hp⟩ := (isUniversalHomeomorphism_iff_charP p hpA f).mp hf
  cases subsingleton_or_nontrivial A with
  | inl h =>
    letI := h
    letI : Subsingleton B := f.codomain_trivial
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun b ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | inr h =>
    letI := h
    letI : CharP A p := (charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpA
    have hi : Function.Injective f := by
      apply (RingHom.injective_iff_ker_eq_bot f).mpr
      apply le_antisymm ?_ bot_le
      intro a ha
      obtain ⟨n, hn⟩ := hk ha
      apply Ideal.mem_bot.mpr
      apply (PerfectRing.bijective_frobenius (M := A) (p := p ^ n)).injective
      rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
      exact pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hn
    haveI : Nontrivial B := hi.nontrivial
    letI : CharP B p := (charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast f, hpA, map_zero])
    refine ⟨hi, fun b ↦ ?_⟩
    obtain ⟨n, a, ha⟩ := hp b
    obtain ⟨x, hx⟩ := (bijective_iterateFrobenius A p n).surjective a
    refine ⟨x, ?_⟩
    apply iterateFrobenius_inj B p n
    change (f x) ^ (p ^ n) = b ^ (p ^ n)
    rw [← map_pow, ← iterateFrobenius_def, hx, ha]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：純非分離な体の拡大は普遍同相。
方針：両側の Spec の唯一の点で剰余体の射を同定する。 -/
theorem isUniversalHomeomorphism_of_isPurelyInseparable (K L : Type u) [Field K] [Field L]
    [Algebra K L] [IsPurelyInseparable K L] : IsUniversalHomeomorphism (algebraMap K L) := by
  refine ⟨Algebra.IsIntegral.isIntegral, ?_, ?_, ?_⟩
  · intro P
    exact ⟨⟨⊥, inferInstance⟩, Subsingleton.elim _ _⟩
  · intro P Q _
    exact Subsingleton.elim _ _
  · intro Q
    let P := PrimeSpectrum.comap (algebraMap K L) Q
    let eK := P.asIdeal.algEquivResidueFieldOfField
    let eL := Q.asIdeal.algEquivResidueFieldOfField
    have hKL : (algebraMap K L).IsPurelyInseparable :=
      RingHom.isPurelyInseparable_algebraMap_iff.mpr inferInstance
    have h := ((purelyInseparable_of_surjective eK.symm.toRingEquiv.toRingHom
      eK.symm.surjective).comp hKL).comp
      (purelyInseparable_of_surjective eL.toRingEquiv.toRingHom eL.surjective)
    have he : eL.toRingEquiv.toRingHom.comp
        ((algebraMap K L).comp eK.symm.toRingEquiv.toRingHom) =
        Ideal.ResidueField.map P.asIdeal Q.asIdeal (algebraMap K L) rfl := by
      apply Ideal.ResidueField.ringHom_ext
      ext a
      simpa only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] using
        congrArg (fun x ↦ eL (algebraMap K L x)) (eK.symm_apply_apply a)
    rw [he] at h
    exact h

end SerrePositivity.CommutativeAlgebra
