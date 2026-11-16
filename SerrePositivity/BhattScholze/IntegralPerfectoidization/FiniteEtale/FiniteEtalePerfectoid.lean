module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Perfection
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# 有限エタール代数の整 perfectoid 性

## 概要
整 perfectoid 環上の有限エタール代数は整 perfectoid（G-A8-6）。

## 方針
mod p の相対 Frobenius の比較から tilt の第 0 射影の核を移す。
有限射影性で p 進完備性と p ねじれの持ち上げを得て、Fontaine 核の生成元を移す。

## 規約
`IsIntegralPerfectoid` に従い、零環と p ねじれを持つ場合を含む。

## 使われ方
BS 著者版 §10 の整代数の perfectoid 化で有限エタールな場合を扱う。
-/

@[expose] public noncomputable section
universe u

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open scoped _root_.TensorProduct _root_.BigOperators

section RelativeFrobenius

open _root_.Algebra TensorProduct
open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private def _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEquiv (I : Ideal A) :
    (A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B ⧸ I.map (algebraMap A B) := by
  let e := Algebra.TensorProduct.lid A B
  have hmap : I.map (algebraMap A B) =
      (I.map (algebraMap A (A ⊗[A] B))).map (e.toRingEquiv : A ⊗[A] B →+* B) := by
    rw [Ideal.map_map]
    congr 1
    ext a
    change algebraMap A B a = e (algebraMap A (A ⊗[A] B) a)
    exact (e.commutes a).symm
  refine { (quotientTensorEquiv (R := A) A B A I).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e.toRingEquiv hmap) with commutes' := ?_ }
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.quotientEquiv _ _ e.toRingEquiv hmap)
      (quotientTensorEquiv (R := A) A B A I (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : B))) =
      algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk I a)
  rw [quotientTensorEquiv_apply_tmul]
  rw [Ideal.quotientEquiv_mk]
  change Ideal.Quotient.mk _ (e (a ⊗ₜ[A] (1 : B))) = _
  rw [Algebra.TensorProduct.lid_tmul]
  rw [Algebra.smul_def, mul_one]
  rfl

private theorem _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEtale (I : Ideal A) [Algebra.Etale A B] :
    Algebra.Etale (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  exact Algebra.Etale.of_equiv (_root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEquiv (B := B) I)

private theorem _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeFinite (I : Ideal A) [Module.Finite A B] :
    Module.Finite (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  let e := _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEquiv (B := B) I
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

variable (p : ℕ) [Fact p.Prime]

private theorem _root_.SerrePositivity.BhattScholze.Almost.bijective_of_etale_of_pow_in_range (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [CharP B p] [Algebra.Etale A B]
    (hpow : ∀ b : B, ∃ a : A, algebraMap A B a = b ^ p)
    (hker : ∀ a ∈ RingHom.ker (algebraMap A B), IsNilpotent a) :
    Function.Bijective (algebraMap A B) := by
  let : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨a, ha⟩ := hpow b
    refine ⟨Polynomial.X ^ p - Polynomial.C a,
      Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, ?_⟩
    simp [ha]⟩
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_comap_surjective (fun P => by
    let : P.asIdeal.IsPrime := P.isPrime
    have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ P.asIdeal := fun a ha => by
      obtain ⟨n, hn⟩ := hker a ha
      exact P.isPrime.isRadical ⟨n, hn ▸ P.asIdeal.zero_mem⟩
    obtain ⟨Q, _, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal
      (⊥ : Ideal B) hle
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩)
  let M := B ⊗[A] B
  let l : B →ₐ[A] M := Algebra.TensorProduct.includeLeft
  let m : M →ₐ[A] B := Algebra.TensorProduct.lmul' A
  have hml (b : B) : m (l b) = b := AlgHom.congr_fun Algebra.TensorProduct.lmul'_comp_includeLeft b
  have hl : Function.Injective l := Function.LeftInverse.injective hml
  let : CharP M p := charP_of_injective_ringHom (f := l.toRingHom) hl p
  let : ExpChar M p := .prime (Fact.out : p.Prime)
  have hpowM (z : M) : z ^ p = l (m z ^ p) := by
    refine _root_.TensorProduct.inductionOn (motive := fun w : M => w ^ p = l (m w ^ p)) z ?_ ?_
    · intro x y
      obtain ⟨a, ha⟩ := hpow y
      change (x ⊗ₜ[A] y) ^ p = l (m (x ⊗ₜ[A] y) ^ p)
      have hm : m (x ⊗ₜ[A] y) = x * y :=
        Algebra.TensorProduct.lmul'_apply_tmul (R := A) x y
      rw [Algebra.TensorProduct.tmul_pow, hm, mul_pow, ← ha]
      change (x ^ p) ⊗ₜ[A] algebraMap A B a = (x ^ p * algebraMap A B a) ⊗ₜ[A] (1 : B)
      calc
        (x ^ p) ⊗ₜ[A] algebraMap A B a = (x ^ p) ⊗ₜ[A] (a • (1 : B)) := by
          rw [Algebra.algebraMap_eq_smul_one]
        _ = (a • x ^ p) ⊗ₜ[A] (1 : B) := (TensorProduct.smul_tmul a _ _).symm
        _ = (x ^ p * algebraMap A B a) ⊗ₜ[A] (1 : B) := by
          rw [Algebra.smul_def, mul_comm (algebraMap A B a)]
    · intro x y hx hy
      rw [add_pow_expChar, map_add, add_pow_expChar, map_add, hx, hy]
  -- The étale diagonal ideal is generated by an idempotent, whose pth power vanishes.
  have hzero : KaehlerDifferential.ideal A B = ⊥ := by
    obtain ⟨e, he, hsp⟩ :=
      (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp
        ((Ideal.cotangent_subsingleton_iff _).mp
          (inferInstance : Subsingleton (KaehlerDifferential A B)))
    have hem : m e = 0 := by
      change e ∈ KaehlerDifferential.ideal A B
      rw [hsp]
      exact Ideal.mem_span_singleton_self e
    have hep : e ^ p = 0 := by
      rw [hpowM, hem, zero_pow (Fact.out : p.Prime).ne_zero, map_zero]
    have he0 : e = 0 := he.eq_zero_of_isNilpotent ⟨p, hep⟩
    simp [hsp, he0]
  have hmi : Function.Injective m := (RingHom.injective_iff_ker_eq_bot _).mpr hzero
  refine ⟨FaithfulSMul.algebraMap_injective A B, ?_⟩
  apply Module.FaithfullyFlat.surjective_of_tensorProduct (S := B)
  intro z
  exact ⟨m z, hmi (hml _)⟩


/-- 半完全環上のエタール代数の Frobenius は全射で、核は基礎から拡大する。 -/
theorem _root_.SerrePositivity.BhattScholze.Almost.etale_frobenius_surjective_ker (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [CharP A p] [CharP B p] [Algebra.Etale A B]
    (hF : Function.Surjective (frobenius A p)) :
    Function.Surjective (frobenius B p) ∧
      RingHom.ker (frobenius B p) = (RingHom.ker (frobenius A p)).map (algebraMap A B) := by
  let I := RingHom.ker (frobenius A p)
  let J := I.map (algebraMap A B)
  let e := RingHom.quotientKerEquivOfSurjective hF
  have hJ : J ≤ RingHom.ker (frobenius B p) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    have ha0 : a ^ p = 0 := ha
    change (algebraMap A B a) ^ p = 0
    rw [← map_pow, ha0, map_zero]
  let g := Ideal.Quotient.lift J (frobenius B p) hJ
  have hcomp : g.comp (algebraMap (A ⧸ I) (B ⧸ J)) =
      (algebraMap A B).comp e.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (algebraMap A B a) ^ p = algebraMap A B (a ^ p)
    exact (map_pow _ _ _).symm
  have hE : (g.comp (algebraMap (A ⧸ I) (B ⧸ J))).Etale := by
    rw [hcomp]
    exact RingHom.Etale.stableUnderComposition _ _
      (.of_bijective e.bijective) (RingHom.etale_algebraMap.mpr inferInstance)
  let : Algebra (A ⧸ I) (B ⧸ J) := Ideal.Quotient.algebraQuotientMapQuotient
  let : Algebra (B ⧸ J) B := g.toAlgebra
  let : Algebra (A ⧸ I) B := (g.comp (algebraMap (A ⧸ I) (B ⧸ J))).toAlgebra
  let : @IsScalarTower (A ⧸ I) (B ⧸ J) B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := A ⧸ I) (S := B ⧸ J) (A := B) (fun _ => rfl)
  let : Algebra.Etale (A ⧸ I) B := hE
  let : Algebra.Etale (A ⧸ I) (B ⧸ J) := _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEtale I
  let : Algebra.Etale (B ⧸ J) B := Algebra.Etale.of_restrictScalars (A ⧸ I) (B ⧸ J) B
  have hg : Function.Bijective g := _root_.SerrePositivity.BhattScholze.Almost.bijective_of_etale_of_pow_in_range p (B ⧸ J) B
    (fun b => ⟨Ideal.Quotient.mk J b, rfl⟩) (fun b hb => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb0 : b ^ p = 0 := hb
      exact ⟨p, by rw [← map_pow, hb0, map_zero]⟩)
  refine ⟨hg.surjective.comp Ideal.Quotient.mk_surjective, le_antisymm ?_ hJ⟩
  intro b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hg.injective ((show g (Ideal.Quotient.mk J b) = 0 from hb).trans (map_zero g).symm)

end RelativeFrobenius

section TiltKernel

variable (p : ℕ) [Fact p.Prime]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [CharP A p] [CharP B p]

private theorem _root_.SerrePositivity.BhattScholze.Almost.perfection_coeff_zero_kernel_eq_map_of_frobenius
    [Module.Finite A B] (hA : Function.Surjective (frobenius A p))
    (hB : Function.Surjective (frobenius B p)) (a : A) (ha : a ^ p = 0)
    (hk : RingHom.ker (frobenius B p) = Ideal.span {algebraMap A B a}) :
    RingHom.ker (Perfection.coeff B p 0) =
      (RingHom.ker (Perfection.coeff A p 0)).map (Perfection.map p (algebraMap A B)) := by
  classical
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := B)
  choose t ht using fun i => Perfection.coeff_surjective hB 0 (v i)
  let f (n : ℕ) := Fintype.linearCombination A (fun i : Fin m => Perfection.coeff B p n (t i))
  let F (w : Fin m → A) : Fin m → A := fun i => w i ^ p
  have hF : Function.Surjective F := fun w => ⟨fun i => (hA (w i)).choose,
    funext fun i => (hA (w i)).choose_spec⟩
  have hcomm (n : ℕ) (w : Fin m → A) : f (n + 1) w ^ p = f n (F w) := by
    simp only [f, F, Fintype.linearCombination_apply, sum_pow_char, Algebra.smul_def, mul_pow,
      ← map_pow (algebraMap A B), Perfection.coeff_pow_p']
  -- The chosen generators remain generators at each level by Nakayama.
  have hsurj (n : ℕ) : Function.Surjective (f n) := by
    induction n with
    | zero =>
      intro b
      have hb : b ∈ Submodule.span A (Set.range v) := hv ▸ Submodule.mem_top
      obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hb
      exact ⟨w, by simpa only [f, Fintype.linearCombination_apply, ht] using hw⟩
    | succ n ih =>
      let I : Ideal A := Ideal.span {a}
      have hI : I ≤ (⊥ : Ideal A).jacobson := by
        apply le_trans _ Ideal.radical_le_jacobson
        exact (Ideal.span_singleton_le_iff_mem _).mpr ⟨p, ha ▸ Submodule.zero_mem _⟩
      apply (f (n + 1)).surjective_of_surjective_comp_mkQ I hI
      intro y
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨w, hw⟩ := ih (b ^ p)
      obtain ⟨w', rfl⟩ := hF w
      refine ⟨w', ?_⟩
      change Submodule.Quotient.mk (f (n + 1) w') = Submodule.Quotient.mk b
      apply (Submodule.Quotient.eq _).mpr
      have hmem : f (n + 1) w' - b ∈ RingHom.ker (frobenius B p) := by
        change (f (n + 1) w' - b) ^ p = 0
        rw [sub_pow_char, hcomm, hw, sub_self]
      rw [hk] at hmem
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, I, Ideal.map_span,
        Set.image_singleton] using hmem
  apply le_antisymm
  · intro x hx
    have hstep (n : ℕ) (w : Fin m → A) (hw : f n w = Perfection.coeff B p n x) :
        ∃ w', f (n + 1) w' = Perfection.coeff B p (n + 1) x ∧ F w' = w := by
      obtain ⟨w', rfl⟩ := hF w
      have hmem : f (n + 1) w' - Perfection.coeff B p (n + 1) x ∈
          RingHom.ker (frobenius B p) := by
        change (f (n + 1) w' - Perfection.coeff B p (n + 1) x) ^ p = 0
        rw [sub_pow_char, hcomm, hw, Perfection.coeff_pow_p', sub_self]
      rw [hk] at hmem
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
      obtain ⟨z, hz⟩ := hsurj (n + 1) b
      refine ⟨w' - a • z, ?_, ?_⟩
      · rw [map_sub, map_smul, hz, Algebra.smul_def, ← hb, sub_sub_cancel]
      · ext i
        change (w' i - a * z i) ^ p = w' i ^ p
        rw [sub_pow_char, mul_pow, ha, zero_mul, sub_zero]
    let L (n : ℕ) := {w : Fin m → A // f n w = Perfection.coeff B p n x}
    let step (n : ℕ) (w : L n) : L (n + 1) :=
      ⟨(hstep n w.val w.property).choose, (hstep n w.val w.property).choose_spec.1⟩
    let w (n : ℕ) : L n := Nat.rec ⟨0, by rw [map_zero]; exact hx.symm⟩ step n
    let c (i : Fin m) : Perfection A p := ⟨fun n => (w n).val i, fun n =>
      congrFun (hstep n (w n).val (w n).property).choose_spec.2 i⟩
    have he : x = ∑ i, Perfection.map p (algebraMap A B) (c i) * t i := by
      apply Perfection.ext
      intro n
      rw [map_sum]
      simp only [map_mul]
      change Perfection.coeff B p n x =
        ∑ i, algebraMap A B ((w n).val i) * Perfection.coeff B p n (t i)
      simpa only [f, Fintype.linearCombination_apply, Algebra.smul_def] using ((w n).property).symm
    rw [he]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (show c i ∈
      RingHom.ker (Perfection.coeff A p 0) from rfl))
  · apply Ideal.map_le_iff_le_comap.mpr
    intro c hc
    change algebraMap A B (Perfection.coeff A p 0 c) = 0
    rw [show Perfection.coeff A p 0 c = 0 from hc, map_zero]

end TiltKernel

section FontaineKernel

variable (p : ℕ) [Fact p.Prime]
variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : T))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : T)}) T]

open scoped _root_.BigOperators

private theorem _root_.SerrePositivity.BhattScholze.Almost.fontaineKer_eq_of_map_and_torsion [Module.Finite R T] [Module.Projective R T]
    (hR : Function.Surjective (frobenius (ModP R p) p))
    (hT : Function.Surjective (frobenius (ModP T p) p))
    (d : WittVector p (PreTilt R p))
    (hd : (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hdker : RingHom.ker (WittVector.fontaineTheta R p) = Ideal.span {d})
    (hgen : RingHom.ker (PreTilt.coeff 0 : PreTilt T p →+* ModP T p) =
      Ideal.span {Perfection.map p (_root_.SerrePositivity.modPMap p (algebraMap R T)) (d.coeff 0)}) :
    RingHom.ker (WittVector.fontaineTheta T p) =
      Ideal.span {WittVector.map (Perfection.map p (_root_.SerrePositivity.modPMap p (algebraMap R T))) d} := by
  classical
  let W := WittVector p (PreTilt T p)
  let L := Perfection.map p (_root_.SerrePositivity.modPMap p (algebraMap R T))
  let g : WittVector p (PreTilt R p) →+* W := WittVector.map L
  let θ := WittVector.fontaineTheta T p
  let θR := WittVector.fontaineTheta R p
  let e : W := g d
  let J : Ideal W := Ideal.span {e}
  let q := Ideal.Quotient.mk J
  have hJ : J ≤ RingHom.ker θ := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have hd0 : θR d = 0 :=
      show d ∈ RingHom.ker θR from hdker ▸ Ideal.mem_span_singleton_self _
    change θ (g d) = 0
    rw [show θ (g d) = algebraMap R T (θR d) from
      RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.fontaineTheta_natural p (algebraMap R T)) d, hd0, map_zero]
  have hθg (x : WittVector p (PreTilt R p)) : θ (g x) = algebraMap R T (θR x) :=
    RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.fontaineTheta_natural p (algebraMap R T)) x
  -- The finite projective splitting gives p-torsion coordinates over R.
  have hlift (t : T) (ht : (p : T) * t = 0) : ∃ b : W, θ b = t ∧ (p : W) * b ∈ J := by
    obtain ⟨n, f, s, _, _, hfs⟩ := Module.Finite.exists_comp_eq_id_of_projective R T
    have hz (i : Fin n) : (p : R) * s t i = 0 := by
      have hm : (p : R) • t = 0 := by simpa only [Algebra.smul_def, map_natCast] using ht
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul, map_zero, Pi.zero_apply] using
        congrFun (congrArg s hm) i
    choose a ha using fun i => surjective_fontaineTheta hR (s t i)
    choose b hb using fun i : Fin n =>
      surjective_fontaineTheta hT (f (Pi.single i 1))
    refine ⟨∑ i, g (a i) * b i, ?_, ?_⟩
    · have hf : ∑ i : Fin n, (s t i) • Pi.single i (1 : R) = s t := by
        ext i
        simp [Pi.single_apply]
      calc
        θ (∑ i, g (a i) * b i) = ∑ i, (s t i) • f (Pi.single i 1) := by
          simp only [map_sum, map_mul, hθg, θR, θ, ha, hb, Algebra.smul_def]
        _ = f (∑ i, (s t i) • Pi.single i (1 : R)) := by simp only [map_sum, map_smul]
        _ = t := by rw [hf]; exact LinearMap.congr_fun hfs t
    · rw [Finset.mul_sum]
      apply Ideal.sum_mem
      intro i _
      have hm : (p : WittVector p (PreTilt R p)) * a i ∈ RingHom.ker θR := by
        change θR ((p : WittVector p (PreTilt R p)) * a i) = 0
        rw [map_mul, map_natCast, ha, hz]
      rw [hdker] at hm
      have he : g ((p : WittVector p (PreTilt R p)) * a i) ∈ J := by
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hm
        apply Ideal.mem_span_singleton.mpr
        exact ⟨g r, by rw [hr, map_mul]⟩
      rw [map_mul, map_natCast] at he
      rw [← mul_assoc]
      exact J.mul_mem_right _ he
  have hstep (x : W) (hx : θ x = 0) : ∃ z : W, θ z = 0 ∧ q x = (p : W ⧸ J) * q z := by
    have hm : x.coeff 0 ∈ RingHom.ker (PreTilt.coeff 0 : PreTilt T p →+* ModP T p) := by
      change PreTilt.coeff 0 (x.coeff 0) = 0
      rw [← WittVector.mk_fontaineTheta, show WittVector.fontaineTheta T p x = 0 from hx,
        map_zero]
    rw [hgen] at hm
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hm
    let y : W := e * WittVector.teichmuller p r
    have hy : y ∈ J := Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
    have hp : x - y ∈ Ideal.span {(p : W)} := by
      apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
      change (WittVector.constantCoeff : W →+* PreTilt T p) (x - y) = 0
      dsimp only [y]
      rw [map_sub, map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        show e.coeff 0 = L (d.coeff 0) from rfl, hr, sub_self]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hp
    have hw0 : (p : T) * θ w = 0 := by
      rw [← map_natCast θ, ← map_mul, ← hw, map_sub, hx, show θ y = 0 from hJ hy, sub_zero]
    obtain ⟨b, hb, hbJ⟩ := hlift (θ w) hw0
    refine ⟨w - b, by rw [map_sub, hb, sub_self], ?_⟩
    have heq : q x = q ((p : W) * w) := by
      rw [← hw, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hy, sub_zero]
    rw [heq, ← map_natCast q, ← map_mul, mul_sub, map_sub,
      Ideal.Quotient.eq_zero_iff_mem.mpr hbJ, sub_zero]
  let hd' : (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt T p)).IsDistinguished e :=
    (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff p _ _).mpr
      (((_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff p _ _).mp hd).map L)
  let := (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p (PreTilt T p)).distinguished_quotient_isAdicComplete hd'
  apply le_antisymm (fun x hx => ?_) hJ
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsHausdorff.haus (I := Ideal.span {(p : W ⧸ J)}) inferInstance
  intro n
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
    Submodule.restrictScalars_self, Ideal.span_singleton_pow]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨z, hz, heq⟩ := hstep x hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (ih z hz)
    exact Ideal.mem_span_singleton.mpr ⟨b, by rw [heq, hb, pow_succ', mul_assoc]⟩

end FontaineKernel


private theorem _root_.SerrePositivity.BhattScholze.Almost.coeffZeroKer_eq_span_of_fontaineKer {S : Type u} [CommRing S]
    (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : S))]
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (d : WittVector p (PreTilt S p))
    (hd : RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {d}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {d.coeff 0} := by
  let θ := WittVector.fontaineTheta S p
  apply le_antisymm
  · intro z hz
    have hm : z.untilt ∈ Ideal.span {(p : S)} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [PreTilt.mk_untilt_eq_coeff_zero, show PreTilt.coeff 0 z = 0 from hz]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hm
    obtain ⟨x, hx⟩ := surjective_fontaineTheta hF s
    have hw : WittVector.teichmuller p z - (p : WittVector p (PreTilt S p)) * x ∈
        RingHom.ker θ := by
      change θ _ = 0
      rw [map_sub, WittVector.fontaineTheta_teichmuller, map_mul, map_natCast, hx, hs, sub_self]
    rw [hd] at hw
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hw
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y.coeff 0, ?_⟩
    simpa only [map_sub, map_mul, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.coeff_p_zero, zero_mul, sub_zero]
      using congrArg (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _) hy
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h : θ d = 0 := show d ∈ RingHom.ker θ from hd ▸ Ideal.mem_span_singleton_self _
    change PreTilt.coeff 0 (d.coeff 0) = 0
    rw [← WittVector.mk_fontaineTheta, h, map_zero]

/-- 整 perfectoid 環上の有限エタール代数は整 perfectoid（G-A8-6）。 -/
theorem _root_.SerrePositivity.BhattScholze.Almost.isIntegralPerfectoid_of_finiteEtale (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T] :
    _root_.SerrePositivity.IsIntegralPerfectoid T p := by
  classical
  by_cases hsub : Subsingleton T
  · exact Or.inl hsub
  let : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsub
  rcases hR with hR0 | ⟨hpR, hcR, ⟨π, uπ, hπ⟩, hFR, hkerR⟩
  · apply (hsub (subsingleton_of_zero_eq_one ?_)).elim
    simpa only [map_zero, map_one] using
      congrArg (algebraMap R T) (@Subsingleton.elim R hR0 0 1)
  let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
  let := hcR
  have hR : _root_.SerrePositivity.IsIntegralPerfectoid R p := Or.inr ⟨hpR, hcR, ⟨π, uπ, hπ⟩, hFR, hkerR⟩
  let : Module.FinitePresentation R T := .of_finite_of_finitePresentation R T
  let : Module.Projective R T := Module.Flat.projective_of_finitePresentation
  let I : Ideal R := Ideal.span {(p : R)}
  have hI : I.map (algebraMap R T) = Ideal.span {(p : T)} := by
    simp only [I, Ideal.map_span, Set.image_singleton, map_natCast]
  have hcT : IsAdicComplete (Ideal.span {(p : T)}) T := by
    rw [← hI, IsAdicComplete.map_algebraMap_iff]
    obtain ⟨n, _, s, _, hs, _⟩ := Module.Finite.exists_comp_eq_id_of_projective R T
    let := _root_.SerrePositivity.isAdicComplete_function (M := R) (ι := Fin n) I
    let := _root_.SerrePositivity.isHausdorff_of_injective_linearMap I s hs
    let := _root_.SerrePositivity.isPrecomplete_finite I T
    exact {}
  let := hcT
  have hpT : ¬ IsUnit (p : T) := by
    intro hp
    have h : Ideal.span {(p : T)} = ⊤ := Ideal.span_singleton_eq_top.mpr hp
    have hc : IsHausdorff (⊤ : Ideal T) T := h ▸ hcT.toIsHausdorff
    have h10 : (1 : T) = 0 := IsHausdorff.haus hc 1 (fun n => by
      rw [SModEq.zero]
      simp [Ideal.top_pow])
    exact one_ne_zero h10
  let : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
  let A := ModP R p
  let B := ModP T p
  let f := _root_.SerrePositivity.modPMap p (algebraMap R T)
  let : Algebra A B := f.toAlgebra
  let E : (T ⧸ I.map (algebraMap R T)) ≃ₐ[A] B := by
    refine { (Ideal.quotEquivOfEq hI) with commutes' := ?_ }
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
    change Ideal.quotEquivOfEq hI (Ideal.Quotient.mk _ (algebraMap R T r)) =
      Ideal.Quotient.mk _ (algebraMap R T r)
    exact Ideal.quotEquivOfEq_mk _ _
  let : Algebra.Etale A B := by
    let := _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeEtale (B := T) I
    exact Algebra.Etale.of_equiv E
  let : Module.Finite A B := by
    let := _root_.SerrePositivity.BhattScholze.Almost.quotientBaseChangeFinite (B := T) I
    exact Module.Finite.of_surjective E.toLinearMap E.surjective
  obtain ⟨hFT, hFTker⟩ := _root_.SerrePositivity.BhattScholze.Almost.etale_frobenius_surjective_ker p A B hFR
  let a : A := Ideal.Quotient.mk I π
  have ha : a ^ p = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨↑(uπ⁻¹), by
      rw [hπ, mul_comm (↑uπ : R) (π ^ p), mul_assoc, Units.mul_inv, mul_one]⟩
  have hAker : RingHom.ker (frobenius A p) = Ideal.span {a} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hr : r ^ p ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_pow]
        exact hz
      have hIπ : I ≤ Ideal.span {π ^ p} := (Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mem_span_singleton.mpr ⟨uπ, hπ.trans (mul_comm _ _)⟩)
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp
        (hR.frobenius_kernel_of_unit_root R p π uπ hπ r (hIπ hr))
      apply Ideal.mem_span_singleton.mpr
      exact ⟨Ideal.Quotient.mk I s, by rw [hs, map_mul]⟩
    · exact (Ideal.span_singleton_le_iff_mem _).mpr ha
  rw [hAker, Ideal.map_span, Set.image_singleton] at hFTker
  obtain ⟨d, hd, hdker⟩ :=
    _root_.SerrePositivity.BhattScholze.exists_distinguished_fontaine_kernel_generator R p hFR hkerR π uπ hπ
  have hgen := _root_.SerrePositivity.BhattScholze.Almost.perfection_coeff_zero_kernel_eq_map_of_frobenius p hFR hFT a ha hFTker
  let L : PreTilt R p →+* PreTilt T p := Perfection.map p (_root_.SerrePositivity.modPMap p (algebraMap R T))
  change RingHom.ker (PreTilt.coeff 0 : PreTilt T p →+* ModP T p) =
    (RingHom.ker (PreTilt.coeff 0 : PreTilt R p →+* ModP R p)).map
      L at hgen
  rw [_root_.SerrePositivity.BhattScholze.Almost.coeffZeroKer_eq_span_of_fontaineKer p hFR d hdker, Ideal.map_span,
    Set.image_singleton] at hgen
  refine Or.inr ⟨hpT, hcT, ⟨algebraMap R T π, Units.map (algebraMap R T) uπ, ?_⟩, hFT, ?_⟩
  · change (p : T) = algebraMap R T (uπ : R) * (algebraMap R T π) ^ p
    simpa only [map_natCast, map_mul, map_pow] using congrArg (algebraMap R T) hπ
  · rw [_root_.SerrePositivity.BhattScholze.Almost.fontaineKer_eq_of_map_and_torsion p hFR hFT d hd hdker hgen]
    exact ⟨_, rfl⟩

end SerrePositivity.BhattScholze.Perfectoidization.Derived
