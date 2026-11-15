module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcPerfectoidBase
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.CharacteristicP
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# 階数 1 の付値環の perfectoid 拡大

## 概要
p 完備な階数 1 の付値環を、p の両立する p 冪根を持つ整 perfectoid 付値環へ忠実平坦に拡大する。

## 方針
分数体の代数閉包へ付値を延長する。代数関係式の係数の一つを 1 に正規化し、
非零素イデアルでの剰余が代数的であることから階数 1 を保つ。
標数 p では完全性を使い、混標数では p 進完備化の mod p と p の根を使う。

## 規約
試験環と拡大は同じ宇宙に置く。体から出発する分岐では一変数の冪級数環を経由する。

## 使われ方
BS 著者版 Lemma 8.8 の証明の底変換と、Proposition 8.10 の証明の試験付値環。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.CategoryTheory _root_.IsLocalRing _root_.Polynomial
open scoped _root_.nonZeroDivisors

section RankOne

variable {V W : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra V W]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.finite_coeff_dvd (P : V[X]) {s : Finset ℕ} (hs : s.Nonempty) :
    ∃ n ∈ s, ∀ m ∈ s, P.coeff n ∣ P.coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert j s hj ih =>
    by_cases h : s.Nonempty
    · obtain ⟨n, hn, hmin⟩ := ih h
      rcases ValuationRing.dvd_total (P.coeff j) (P.coeff n) with hd | hd
      · refine ⟨j, Finset.mem_insert_self _ _, ?_⟩
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact dvd_rfl
        · exact hd.trans (hmin _ hm)
      · refine ⟨n, Finset.mem_insert_of_mem hn, ?_⟩
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hd
        · exact hmin _ hm
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      exact ⟨j, by simp, by simp⟩

omit [IsLocalRing W] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.algebraic_has_relation_with_unit_coeff
    (hinj : Function.Injective (algebraMap V W)) {x : W} (hx : IsAlgebraic V x) :
    ∃ P : V[X], aeval x P = 0 ∧ ∃ n, P.coeff n = 1 := by
  obtain ⟨P, hP, hx⟩ := hx
  obtain ⟨n, hn, hdvd⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.finite_coeff_dvd P (support_nonempty.mpr hP)
  have hn0 : P.coeff n ≠ 0 := mem_support_iff.mp hn
  have hdiv : C (P.coeff n) ∣ P := (C_dvd_iff_dvd_coeff _ _).mpr fun m => by
    by_cases hm : m ∈ P.support
    · exact hdvd m hm
    · rw [notMem_support_iff.mp hm]
      exact dvd_zero _
  obtain ⟨Q, hQ⟩ := hdiv
  have hcoeff := congrArg (fun R : V[X] => R.coeff n) hQ
  rw [coeff_C_mul] at hcoeff
  have hcoeff' : Q.coeff n = 1 := mul_left_cancel₀ hn0 (hcoeff.symm.trans (mul_one _).symm)
  rw [hQ, map_mul, aeval_C] at hx
  have hNZ : algebraMap V W (P.coeff n) ≠ 0 := fun h =>
    hn0 (hinj (h.trans (map_zero _).symm))
  exact ⟨Q, (mul_eq_zero.mp hx).resolve_left hNZ, n, hcoeff'⟩

/-- 階数 1 の付値環の局所代数的拡大で、整域であるものの Krull 次元は 1。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_dim_of_algebraic [Algebra.IsAlgebraic V W]
    [IsLocalHom (algebraMap V W)] (hinj : Function.Injective (algebraMap V W))
    (hV : ringKrullDim V = 1) : ringKrullDim W = 1 := by
  have hV' := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hV
  apply ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
  refine ⟨fun h => hV'.1 ?_, ?_⟩
  · refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
    have ha' : algebraMap V W a ≠ 0 := fun hz => ha (hinj (hz.trans (map_zero _).symm))
    obtain ⟨b, hb⟩ := h.mul_inv_cancel ha'
    obtain ⟨c, hc⟩ := isUnit_iff_dvd_one.mp
      (IsUnit.of_map (algebraMap V W) a (isUnit_iff_dvd_one.mpr ⟨b, hb.symm⟩))
    exact ⟨c, hc.symm⟩
  · intro x hx
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro P ⟨hP, hprime⟩
    let : P.IsPrime := hprime
    have hxP : x ∈ P := hP (Ideal.mem_span_singleton_self _)
    obtain ⟨r, hr, hdiv⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := V) x).exists_nonzero_dvd
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    let J := P.comap (algebraMap V W)
    let : J.IsPrime := hprime.comap _
    have hrJ : r ∈ J := by
      obtain ⟨t, ht⟩ := hdiv
      change algebraMap V W r ∈ P
      rw [ht]
      exact P.mul_mem_right t hxP
    have hmJ : maximalIdeal V ≤ J :=
      (hV'.2 r hr).trans
        ((Ideal.IsRadical.radical_le_iff (inferInstance : J.IsPrime).isRadical).mpr
          ((Ideal.span_singleton_le_iff_mem J).mpr hrJ))
    have hJ : J = maximalIdeal V :=
      (Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal V)
        (inferInstance : J.IsPrime).ne_top hmJ).symm
    let k := V ⧸ maximalIdeal V
    let : Field k := Ideal.Quotient.field (maximalIdeal V)
    let q := Ideal.quotientMap P (algebraMap V W) hJ.ge
    let : Algebra k (W ⧸ P) := q.toAlgebra
    have halg : Algebra.IsAlgebraic k (W ⧸ P) := by
      constructor
      intro y
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨Q, hQ, n, hn⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.algebraic_has_relation_with_unit_coeff hinj
        (Algebra.IsAlgebraic.isAlgebraic (R := V) z)
      let Q' := Q.map (Ideal.Quotient.mk (maximalIdeal V))
      refine ⟨Q', ?_, ?_⟩
      · intro h
        have h0 := congrArg (fun F : k[X] => F.coeff n) h
        simp [Q', hn] at h0
      · rw [aeval_def, eval₂_map]
        have hcomp : (algebraMap k (W ⧸ P)).comp (Ideal.Quotient.mk (maximalIdeal V)) =
            (Ideal.Quotient.mk P).comp (algebraMap V W) := rfl
        rw [hcomp, ← hom_eval₂, ← aeval_def, hQ, map_zero]
    let := halg
    have hfield : IsField (W ⧸ P) := isField_of_isIntegral_of_isField' (Field.toIsField k)
    have hmax : P.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr hfield
    exact (eq_maximalIdeal hmax).symm.le

end RankOne

section Perfectoid

variable (p : ℕ) [Fact p.Prime]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuation_dvd_of_pow_dvd {W : Type u} [CommRing W] [IsDomain W] [ValuationRing W]
    {x y : W} (h : x ^ p ∣ y ^ p) : x ∣ y := by
  by_cases hy : y = 0
  · rw [hy]
    exact dvd_zero _
  rcases ValuationRing.dvd_total x y with hxy | ⟨z, hz⟩
  · exact hxy
  obtain ⟨c, hc⟩ := h
  have he : y ^ p * 1 = y ^ p * (z ^ p * c) := by
    calc
      y ^ p * 1 = y ^ p := mul_one _
      _ = x ^ p * c := hc
      _ = y ^ p * (z ^ p * c) := by rw [hz, mul_pow, mul_assoc]
  have hu : IsUnit z := (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
    (isUnit_iff_dvd_one.mpr ⟨c, mul_left_cancel₀ (pow_ne_zero p hy) he⟩)
  rw [hz]
  exact (associated_mul_unit_right _ _ hu).dvd'

/-- 階数 1 の p 完備付値環は、mod p の Frobenius の全射性と p の両立根から整 perfectoid。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing.isPerfectoid_of_roots
    {W : Type u} [CommRing W] (hW : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W)
    (hF : Function.Surjective (fun x : ModP W p => x ^ p))
    (ρ : ℕ → W) (hzero : ρ 0 = (p : W)) (hpow : ∀ n, ρ (n + 1) ^ p = ρ n) :
    _root_.SerrePositivity.IsIntegralPerfectoid W p := by
  let := hW.isDomain
  let := hW.valuationRing
  let := hW.adicComplete
  let P := Ideal.span {(p : W)}
  let q := Ideal.Quotient.mk P
  by_cases hp : (p : W) = 0
  · have hP : P = ⊥ := by simp [P, hp]
    let e : ModP W p ≃+* W := (Ideal.quotEquivOfEq hP).trans (RingEquiv.quotientBot W)
    let : CharP W p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : PerfectRing W p := ⟨⟨frobenius_inj W p, fun x => by
      obtain ⟨y, hy⟩ := hF (e.symm x)
      exact ⟨e y, (map_pow e y p).symm.trans (congrArg e hy |>.trans (e.apply_symm_apply x))⟩⟩⟩
    exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.isIntegralPerfectoid_of_perfectRing_p_eq_zero hp
  have hpu : ¬ IsUnit (p : W) := by
    intro hu
    have htop : IsAdicComplete (⊤ : Ideal W) W :=
      Ideal.span_singleton_eq_top.mpr hu ▸ hW.adicComplete
    exact zero_ne_one (htop.subsingleton.elim 0 1)
  let : Fact (¬ IsUnit (p : W)) := ⟨hpu⟩
  apply _root_.SerrePositivity.isIntegralPerfectoid_of_compatible_p_roots W p (mul_right_injective₀ hp) hF ρ hzero hpow
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hρ : ρ 1 ^ p = (p : W) := (hpow 0).trans hzero
  let J := Ideal.span {ρ 1}
  have hPJ : P ≤ J := by
    apply (Ideal.span_singleton_le_iff_mem J).mpr
    rw [← hρ]
    exact Ideal.pow_mem_of_mem J (Ideal.mem_span_singleton_self _) p (Fact.out : p.Prime).pos
  have hJ : Ideal.span {q (ρ 1)} = J.map q := by rw [Ideal.map_span, Set.image_singleton]
  change (q x) ^ p = 0 ↔ q x ∈ Ideal.span {q (ρ 1)}
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, hJ, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hPJ]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← hρ]
  exact ⟨_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuation_dvd_of_pow_dvd p, fun h => pow_dvd_pow_of_dvd h p⟩

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationSubring_pow_surjective {K : Type u} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : Function.Surjective (fun x : V => x ^ p) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) (Fact.out : p.Prime).pos
  have hval : V.valuation y ^ p ≤ 1 := by
    rw [← map_pow, hy]
    exact (V.valuation_le_one_iff _).mpr x.property
  have hmem : y ∈ V := (V.valuation_le_one_iff _).mp
    ((pow_le_one_iff_of_nonneg (zero_le : 0 ≤ V.valuation y) (Fact.out : p.Prime).ne_zero).mp hval)
  exact ⟨⟨y, hmem⟩, Subtype.ext hy⟩

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.faithfullyFlat_of_local_injective_valuationRing {A B : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f) : f.FaithfullyFlat := by
  let := f.toAlgebra
  let : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom f)
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  let : Module.Flat A B := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- p 完備な階数 1 の付値環は、p の両立する根を持つ整 perfectoid 付値環に忠実平坦に拡大できる。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_valuation_extension (V : CommRingCat.{u})
    (hV : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p V) :
    ∃ (W : CommRingCat.{u}) (e : V →+* W), _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W ∧
      _root_.SerrePositivity.IsIntegralPerfectoid W p ∧ e.FaithfullyFlat ∧
      ∃ ρ : ℕ → W, ρ 0 = (p : W) ∧ ∀ n, ρ (n + 1) ^ p = ρ n := by
  let := hV.isDomain
  let := hV.valuationRing
  let K := FractionRing V
  let L := AlgebraicClosure K
  let f : V →+* L := (algebraMap K L).comp (algebraMap V K)
  obtain ⟨W, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : V →+* W := f.codRestrict W.toSubring hmem
  let : IsLocalHom g := hloc
  have hg : Function.Injective g := by
    intro x y hxy
    exact IsFractionRing.injective V K
      (RingHom.injective (algebraMap K L) (congrArg Subtype.val hxy))
  have hdim : ringKrullDim W = 1 := by
    let := g.toAlgebra
    let : IsLocalHom (algebraMap V W) := inferInstanceAs (IsLocalHom g)
    let : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq V K L)
    let : Algebra.IsAlgebraic V K := IsLocalization.isAlgebraic K V⁰
    let : Algebra.IsAlgebraic V L := Algebra.IsAlgebraic.trans V K L
    let : Algebra.IsAlgebraic V W := Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom V W L) Subtype.val_injective
    exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_dim_of_algebraic hg hV.krullDim_eq_one
  have hflat : g.FaithfullyFlat := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.faithfullyFlat_of_local_injective_valuationRing g hg
  choose τ hτ using _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationSubring_pow_surjective p W
  let ρ : ℕ → W := Nat.rec (p : W) (fun _ x => τ x)
  have hρ (n : ℕ) : ρ (n + 1) ^ p = ρ n := hτ (ρ n)
  by_cases hp : (p : W) = 0
  · have hWc : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W :=
      ⟨inferInstance, inferInstance, hdim, by rw [hp, Ideal.span_singleton_zero]; infer_instance⟩
    have hFq : Function.Surjective (fun x : ModP W p => x ^ p) := by
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      let s := τ r
      have hs : s ^ p = r := hτ r
      refine ⟨Ideal.Quotient.mk _ s, ?_⟩
      change (Ideal.Quotient.mk (Ideal.span {(p : W)}) s) ^ p = Ideal.Quotient.mk _ r
      rw [← map_pow, hs]
    exact ⟨CommRingCat.of W, g, hWc, hWc.isPerfectoid_of_roots p hFq ρ rfl hρ, hflat, ρ, rfl, hρ⟩
  · have hVpu : ¬ IsUnit (p : V) := by
      intro hu
      have htop : IsAdicComplete (⊤ : Ideal V) V :=
        Ideal.span_singleton_eq_top.mpr hu ▸ hV.adicComplete
      exact zero_ne_one (htop.subsingleton.elim 0 1)
    have hpu : ¬ IsUnit (p : W) := fun hu =>
      hVpu (IsUnit.of_map g (p : V) (by rwa [map_natCast]))
    let I := Ideal.span {(p : W)}
    let T := AdicCompletion I W
    let j := algebraMap W T
    obtain ⟨hT, hvT, hdimT, hcomp, hj⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion (p : W) hdim hp hpu
    let := hT
    let hTc : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p T :=
      ⟨hT, hvT, hdimT, by simpa only [map_natCast] using hcomp⟩
    have hFq : Function.Surjective (fun x : ModP T p => x ^ p) := by
      intro x
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hfg : I.FG := Submodule.fg_span_singleton _
      obtain ⟨r, hr⟩ := _root_.SerrePositivity.exists_adicCompletion_algebraMap_sub_mem I hfg 1 t
      have he : Ideal.Quotient.mk (Ideal.span {(p : T)}) (j r) =
          Ideal.Quotient.mk (Ideal.span {(p : T)}) t := by
        apply Ideal.Quotient.eq.mpr
        simpa only [I, pow_one, Ideal.map_span, Set.image_singleton, map_natCast] using hr
      let s := τ r
      have hs : s ^ p = r := hτ r
      refine ⟨Ideal.Quotient.mk _ (j s), ?_⟩
      change (Ideal.Quotient.mk (Ideal.span {(p : T)}) (j s)) ^ p = Ideal.Quotient.mk _ t
      rw [← map_pow, ← map_pow, hs, he]
    have hρT (n : ℕ) : j (ρ (n + 1)) ^ p = j (ρ n) := by rw [← map_pow, hρ]
    exact ⟨CommRingCat.of T, j.comp g, hTc,
      hTc.isPerfectoid_of_roots p hFq (j ∘ ρ) (map_natCast _ _) hρT,
      RingHom.FaithfullyFlat.stableUnderComposition g j hflat hj, j ∘ ρ, map_natCast _ _, hρT⟩

/-- 階数 0 の非単元分岐。冪級数付値環を階数 1 の完全付値環へ忠実平坦に拡大する。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcValuation_extendField (p : ℕ) [Fact p.Prime] [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (a : k) (ha : ¬ IsUnit a) :
    ∃ (V : CommRingCat.{u}) (hV : IsDomain V) (e : k →+* V),
      @ValuationRing V _ hV ∧ ringKrullDim V = 1 ∧ CharP V p ∧ PerfectRing V p ∧
        e.FaithfullyFlat ∧ e a = 0 := by
  let S := PowerSeries k
  let c : k →+* S := PowerSeries.C
  let : CharP S p := charP_of_injective_ringHom (f := c) PowerSeries.C_injective p
  have hSc : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p S :=
    ⟨inferInstance, inferInstance, IsDiscreteValuationRing.ringKrullDim_eq_one S, by
      rw [CharP.cast_eq_zero S p, Ideal.span_singleton_zero]
      infer_instance⟩
  obtain ⟨V, e, hV, hperf, hflat, _⟩ :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_valuation_extension p (CommRingCat.of S) hSc
  let := hV.isDomain
  let : CharP V p := charP_of_injective_ringHom (f := e) hflat.injective p
  have hf : (e.comp c).FaithfullyFlat := by
    let := (e.comp c).toAlgebra
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have ha0 : a = 0 := by
    by_contra h
    exact ha (isUnit_iff_ne_zero.mpr h)
  exact ⟨V, hV.isDomain, e.comp c, hV.valuationRing, hV.krullDim_eq_one, inferInstance,
    hperf.perfectRing_of_charP V p, hf, by rw [ha0, map_zero]⟩

/-- 試験環 V の perfectoid な付値環拡大を選び、その同じ拡大に沿って S₀ への写像を延長する。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_baseExtension_lift (S : Type u) [CommRing S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (V : CommRingCat.{u}) (hV : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p V) (k : S →+* V) :
    ∃ (W : CommRingCat.{u}) (e : V →+* W) (l : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS →+* W),
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W ∧ _root_.SerrePositivity.IsIntegralPerfectoid W p ∧ e.FaithfullyFlat ∧
      l.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtensionUnit p S hS) = e.comp k := by
  obtain ⟨W, e, hW, hperfd, hflat, ρ, hρ0, hρ⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_valuation_extension p V hV
  obtain ⟨b, _⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_toValuationExtension p W hW ρ hρ0 hρ
  obtain ⟨l, hl, _⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_baseExtension_lift_of_map p S hS V W hV hW k e hflat b
  exact ⟨W, e, l, hW, hperfd, hflat, hl⟩

end Perfectoid


end SerrePositivity.BhattScholze.Perfectoidization.Derived
