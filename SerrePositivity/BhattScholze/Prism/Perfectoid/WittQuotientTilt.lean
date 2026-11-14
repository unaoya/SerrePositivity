module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.Perfection
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# 完全な標数 p 環の Witt 環の distinguished 商：mod p と tilt（BS 著者版 Theorem 3.10 の計算）

## 概要
W(k)/(d) の mod p、Frobenius 核の生成元、tilt への係数射とその核・全射性、完全 δ 環の商の mod p Frobenius の全射性。

## 方針
d = [a₀] + p·u（BS 著者版 Lemma 2.33）から p 乗根を作り、Perfection の普遍性で tilt へ持ち上げる。

## 規約
商の完備性は明示した仮定。

## 使われ方
BS 著者版 Theorem 3.10（Prism/Perfectoid/WittQuotientPerfectoid）。
-/

universe u v

/-! ## 完全δ環の商におけるmod p Frobenius全射性

BS 著者版 Theorem 3.10の逆向きの最初の計算。
完備性やFontaine核の単項性を仮定せず、perfectoid性全体は結論しない。
-/

@[expose] public noncomputable section PerfectDeltaQuotientFrobenius

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環からpを零に送る全射環射の終域では、p乗写像が全射。 -/
theorem IsPerfect.surjective_pow_of_surjective_map_p_eq_zero
    {D : DeltaStructure p A} (hD : D.IsPerfect) {B : Type v} [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q) (hp : q (p : A) = 0) :
    Function.Surjective (fun x : B ↦ x ^ p) := by
  intro y
  obtain ⟨a, rfl⟩ := hq y
  obtain ⟨b, hb⟩ := hD.2 a
  refine ⟨q b, ?_⟩
  change (q b) ^ p = q a
  rw [← D.map_frobeniusLift_of_map_p_eq_zero q hp, hb]

/-- 完全δ環の任意のイデアル商はmod pでFrobenius全射。
一般の商を扱い、pねじれのない商に限定しない。 -/
theorem IsPerfect.quotient_mod_p_frobenius_surjective {D : DeltaStructure p A}
    (hD : D.IsPerfect) (I : Ideal A) :
    Function.Surjective (fun x : (A ⧸ I) ⧸ Ideal.span {(p : A ⧸ I)} ↦ x ^ p) := by
  let q := (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ I)})).comp (Ideal.Quotient.mk I)
  apply hD.surjective_pow_of_surjective_map_p_eq_zero q
    (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)
  change Ideal.Quotient.mk (Ideal.span {(p : A ⧸ I)}) (Ideal.Quotient.mk I (p : A)) = 0
  rw [map_natCast]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

end SerrePositivity.BhattScholze.DeltaStructure

end PerfectDeltaQuotientFrobenius

/-! ## distinguished Witt商のp乗根と単元係数

BS 著者版 Lemma 2.33・BS 著者版 Theorem 3.10の具体的なWitt商の計算。
商の完備性とFontaine核の単項性はまだ結論しない。
-/

@[expose] public noncomputable section WittDistinguishedQuotient

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- distinguished Witt元は[x₀]+p*u（u単元）と書ける。
任意の完全係数環でのBS 著者版 Lemma 2.33の具体的な展開。 -/
theorem exists_teichmuller_add_p_mul_unit_of_distinguished (d : WittVector p k)
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    ∃ u : (WittVector p k)ˣ,
      d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * u := by
  have hm : d - WittVector.teichmuller p (d.coeff 0) ∈ Ideal.span {(p : WittVector p k)} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change (WittVector.constantCoeff : WittVector p k →+* k)
      (d - WittVector.teichmuller p (d.coeff 0)) = 0
    rw [map_sub]
    simp
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  have he : d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * y := by
    linear_combination hy
  have h1 : d.coeff 1 = y.coeff 0 ^ p := by
    rw [he, witt_add_coeff_one, WittVector.teichmuller_coeff_pos p _ 1 (by decide)]
    simp only [WittVector.teichmuller_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.coeff_p_zero, zero_mul, WittVector.teichmuller_zero, add_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), zero_add,
      witt_mul_coeff_one, WittVector.coeff_p_one, zero_pow (Fact.out : p.Prime).ne_zero,
      one_mul, CharP.cast_eq_zero]
  have hy0 : IsUnit (y.coeff 0) := by
    apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
    rw [← h1]
    exact (wittDeltaStructure_isDistinguished_iff p k d).mp hd
  obtain ⟨u, hu⟩ := PerfectoidFrobeniusCriterion.witt_isUnit_of_constantCoeff k p y hy0
  exact ⟨u, by simpa only [hu] using he⟩

/-- dを零に送るWitt環からの射の終域で、pは単元倍のp乗。
可除性だけでなく具体的なπと単元の存在を結論する。 -/
theorem exists_unit_mul_pow_p_of_distinguished_map_eq_zero
    (d : WittVector p k) (hd : (wittDeltaStructure p k).IsDistinguished d)
    {S : Type v} [CommRing S] (q : WittVector p k →+* S) (hqd : q d = 0) :
    ∃ (π : S) (v : Sˣ), (p : S) = v * π ^ p := by
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p k d hd
  obtain ⟨a, ha⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (d.coeff 0)
  change a ^ p = d.coeff 0 at ha
  let w := Units.map q.toMonoidHom u
  let π := q (WittVector.teichmuller p a)
  have h : π ^ p + (p : S) * (w : S) = 0 := by
    rw [hu, map_add, map_mul, map_natCast] at hqd
    change q (WittVector.teichmuller p (d.coeff 0)) + (p : S) * q (u : WittVector p k) = 0 at hqd
    change q (WittVector.teichmuller p a) ^ p + (p : S) * q (u : WittVector p k) = 0
    rw [← map_pow, ← map_pow, ha]
    exact hqd
  have hπ : π ^ p = -((p : S) * (w : S)) := eq_neg_of_add_eq_zero_left h
  refine ⟨π, -w⁻¹, ?_⟩
  rw [hπ]
  simp [mul_comm, mul_assoc]

/-- distinguished Witt元による商で、p=単元·π^p。 -/
theorem witt_distinguished_quotient_exists_unit_mul_pow_p (d : WittVector p k)
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    ∃ (π : WittVector p k ⧸ Ideal.span {d}) (v : (WittVector p k ⧸ Ideal.span {d})ˣ),
      (p : WittVector p k ⧸ Ideal.span {d}) = v * π ^ p :=
  exists_unit_mul_pow_p_of_distinguished_map_eq_zero p k d hd (Ideal.Quotient.mk _)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))

end SerrePositivity.BhattScholze

end WittDistinguishedQuotient

/-! ## Witt商のmod pと係数環の商

任意のWitt元dについて(W(k)/(d))/(p)≃k/(d₀)を構成する。
標準商射上の式を明示し、distinguished性や完備性は要求しない。
-/

@[expose] public noncomputable section WittQuotientModP

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt商のmod pを、第0係数による係数環の商に同定する。 -/
def wittQuotientModPEquiv (d : WittVector p k) :
    ((WittVector p k ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) ≃+*
      k ⧸ Ideal.span {d.coeff 0} := by
  let I : Ideal (WittVector p k) := Ideal.span {d}
  let P : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hP : P.map (Ideal.Quotient.mk I) = Ideal.span {(p : WittVector p k ⧸ I)} := by
    simp [P, Ideal.map_span]
  let e := WittVector.quotientPEquiv (p := p) (k := k)
  have hI : Ideal.span {d.coeff 0} = (I.map (Ideal.Quotient.mk P)).map e.toRingHom := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    change Ideal.span {d.coeff 0} =
      Ideal.span {(WittVector.quotientPEquiv (p := p) (k := k)
        (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) d))}
    rfl
  exact ((Ideal.quotEquivOfEq hP.symm).trans (DoubleQuot.quotQuotEquivComm I P)).trans
    (Ideal.quotientEquiv _ _ e hI)

/-- 同型はWitt代表元の第0係数を取る。 -/
@[simp] theorem wittQuotientModPEquiv_mk (d x : WittVector p k) :
    wittQuotientModPEquiv p k d
      (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) x)) =
      Ideal.Quotient.mk (Ideal.span {d.coeff 0}) (x.coeff 0) := by
  rfl

end SerrePositivity.BhattScholze

end WittQuotientModP

/-! ## Witt商mod pのFrobenius核の生成元

係数環の完全性でd₀のp乗根aを選び、W(k)/(d)/pのp乗零化元が[a]の像で
生成されることを証明する。Fontaine核の同定やperfectoid性は別工程。
-/

@[expose] public noncomputable section WittQuotientFrobeniusKernel

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- d₀のp^n乗根aのTeichmüller像は、Witt商mod pの反復Frobenius核を生成する。
dがdistinguishedであるという仮定はこの有限商の計算には不要。 -/
theorem wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span
    (d : WittVector p k) (n : ℕ) (a : k)
    (ha : a ^ (p ^ n) = d.coeff 0)
    (z : (WittVector p k ⧸ Ideal.span {d}) ⧸
      Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) :
    z ^ (p ^ n) = 0 ↔ z ∈ Ideal.span {
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))} := by
  let e := wittQuotientModPEquiv p k d
  let q := Ideal.Quotient.mk (Ideal.span {d.coeff 0})
  let g := Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
    (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))
  have heg : e g = q a := by simp [e, g, q]
  have hqa : (q a) ^ (p ^ n) = 0 := by
    rw [← map_pow, ha]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e z)
    have hbp : b ^ (p ^ n) ∈ Ideal.span {d.coeff 0} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (b ^ (p ^ n)) = 0
      rw [map_pow]
      change q b = e z at hb
      rw [hb, ← map_pow, hz, map_zero]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbp
    obtain ⟨v, hv⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).2 c
    change v ^ (p ^ n) = c at hv
    have hbv : b = a * v := by
      apply (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).1
      change b ^ (p ^ n) = (a * v) ^ (p ^ n)
      rw [mul_pow, ha, hv]
      exact hc
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.symm (q v), ?_⟩
    apply e.injective
    rw [map_mul, heg, RingEquiv.apply_symm_apply, ← map_mul, ← hbv]
    exact hb.symm
  · intro hz
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hz
    change z = g * y at hy
    have hgp : g ^ (p ^ n) = 0 := by
      apply e.injective
      rw [map_pow, heg, hqa, map_zero]
    rw [hy, mul_pow, hgp, zero_mul]

/-- 最初のFrobenius核の具体的な生成元。 -/
theorem wittQuotientModP_pow_eq_zero_iff_mem_span (d : WittVector p k) (a : k)
    (ha : a ^ p = d.coeff 0)
    (z : (WittVector p k ⧸ Ideal.span {d}) ⧸
      Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) :
    z ^ p = 0 ↔ z ∈ Ideal.span {
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))} := by
  simpa only [pow_one] using wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span
    p k d 1 a (by simpa only [pow_one] using ha) z

end SerrePositivity.BhattScholze

end WittQuotientFrobeniusKernel

/-! ## Witt商への係数射とtilt持上げ

S=W(k)/(d)のmod p係数射を、既存Perfection.liftでtiltへ持ち上げる。
untiltの式にはSの古典的p進完備性とpの非可逆性を明示的に仮定する。
-/

@[expose] public noncomputable section WittQuotientTiltMap

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- kからWitt商mod pへの標準係数環射。既存の商同型を逆に使う。 -/
def wittQuotientCoefficientMap (d : WittVector p k) :
    k →+* ModP (WittVector p k ⧸ Ideal.span {d}) p :=
  (wittQuotientModPEquiv p k d).symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {d.coeff 0}))

/-- 標準係数射はTeichmüller元を二度商へ送る式に一致する。 -/
@[simp] theorem wittQuotientCoefficientMap_apply (d : WittVector p k) (x : k) :
    wittQuotientCoefficientMap p k d x =
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p x)) := by
  apply (wittQuotientModPEquiv p k d).injective
  simp [wittQuotientCoefficientMap]

/-- 標準係数射は全射。 -/
theorem wittQuotientCoefficientMap_surjective (d : WittVector p k) :
    Function.Surjective (wittQuotientCoefficientMap p k d) :=
  (wittQuotientModPEquiv p k d).symm.surjective.comp Ideal.Quotient.mk_surjective

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 標準係数射のtiltへの一意な持上げ。一般Perfectionの既存APIを使う。 -/
def wittQuotientTiltMap : k →+* PreTilt (WittVector p k ⧸ Ideal.span {d}) p :=
  Perfection.lift p k _ (wittQuotientCoefficientMap p k d)

/-- tilt持上げの全座標は、逆Frobenius反復の標準係数像。 -/
theorem wittQuotientTiltMap_coeff (n : ℕ) (x : k) :
    PreTilt.coeff n (wittQuotientTiltMap p k d x) =
      wittQuotientCoefficientMap p k d (((_root_.frobeniusEquiv k p).symm : k → k)^[n] x) := rfl

/-- tilt持上げのuntiltは、Witt商のTeichmüller元の標準像。 -/
theorem wittQuotientTiltMap_untilt
    [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
      (WittVector p k ⧸ Ideal.span {d})] (x : k) :
    (wittQuotientTiltMap p k d x).untilt =
      Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p x) := by
  apply Perfection.teichmullerFun_spec
  intro n
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n] x
  refine ⟨Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a), ?_, ?_⟩
  · change Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
      (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a)) =
        PreTilt.coeff n (wittQuotientTiltMap p k d x)
    rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
  · have ha : a ^ (p ^ n) = x := iterate_frobeniusEquiv_symm_pow_p_pow k p x n
    rw [← map_pow, ← map_pow, ha]
    exact SModEq.refl _

/-- d₀のtilt像の第0座標は零。Fontaine核の候補の第0成分に使う。 -/
theorem wittQuotientTiltMap_coeff_zero_d :
    PreTilt.coeff 0 (wittQuotientTiltMap p k d (d.coeff 0)) = 0 := by
  rw [wittQuotientTiltMap_coeff]
  change (wittQuotientModPEquiv p k d).symm
    (Ideal.Quotient.mk (Ideal.span {d.coeff 0}) (d.coeff 0)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]

/-- tiltの第0射影の核の元は、各座標でd₀のtilt像によって割り切れる。
互換的な商の列を構成する工程とは分けた具体的な座標判定。 -/
theorem wittQuotientTilt_kernel_coeff_dvd
    (x : PreTilt (WittVector p k ⧸ Ideal.span {d}) p) (hx : PreTilt.coeff 0 x = 0) (n : ℕ) :
    PreTilt.coeff n (wittQuotientTiltMap p k d (d.coeff 0)) ∣ PreTilt.coeff n x := by
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n] (d.coeff 0)
  have ha : a ^ (p ^ n) = d.coeff 0 := iterate_frobeniusEquiv_symm_pow_p_pow k p _ n
  have hxn : (PreTilt.coeff n x) ^ (p ^ n) = 0 := by
    have h := compatibleRoots_pow p (fun m ↦ PreTilt.coeff m x)
      (fun m ↦ Perfection.coeff_pow_p' x m) 0 n
    simpa only [Nat.zero_add, hx] using h
  have hmem := (wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span p k d n a ha
    (PreTilt.coeff n x)).mp hxn
  apply Ideal.mem_span_singleton.mp
  rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
  exact hmem

end SerrePositivity.BhattScholze

end WittQuotientTiltMap

/-! ## 一般のWitt主イデアル商のtilt射影核

受領F6をmod p商同型に沿って移す。第0係数の正則性は仮定しない。
p非単元の枝を扱い、商の零環にはCharP pを無条件に供給しない。
-/

@[expose] public noncomputable section WittQuotientTiltKernel

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 一般のWitt商のtilt第0射影核はd₀の標準tilt像で生成される。零因子d₀を許す。 -/
theorem wittQuotientTilt_coeff_zero_kernel_eq_span_general :
    RingHom.ker (PreTilt.coeff 0 : PreTilt (WittVector p k ⧸ Ideal.span {d}) p →+*
      ModP (WittVector p k ⧸ Ideal.span {d}) p) =
        Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)} := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let Q := k ⧸ Ideal.span {d.coeff 0}
  let e := wittQuotientModPEquiv p k d
  let : CharP Q p := charP_of_injective_ringHom (f := e.toRingHom) e.injective p
  let L := (Perfection.lift p k Q) (Ideal.Quotient.mk (Ideal.span {d.coeff 0}))
  have hL : Perfection.map p e.symm.toRingHom (L (d.coeff 0)) =
      wittQuotientTiltMap p k d (d.coeff 0) := by
    apply Perfection.ext
    intro n
    rfl
  have hback (x : PreTilt S p) :
      Perfection.map p e.symm.toRingHom (Perfection.map p e.toRingHom x) = x := by
    apply Perfection.ext
    intro n
    exact e.symm_apply_apply _
  apply le_antisymm
  · intro x hx
    let y := Perfection.map p e.toRingHom x
    have hy : y ∈ RingHom.ker (Perfection.coeff Q p 0) := by
      change e (PreTilt.coeff 0 x) = 0
      rw [show PreTilt.coeff 0 x = 0 from hx, map_zero]
    rw [perfection_lift_principal_quotient_kernel k p (d.coeff 0)] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨Perfection.map p e.symm.toRingHom b, ?_⟩
    have h := congrArg (Perfection.map p e.symm.toRingHom) hb
    rw [map_mul, hL, hback] at h
    exact h
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact wittQuotientTiltMap_coeff_zero_d p k d

end SerrePositivity.BhattScholze

end WittQuotientTiltKernel

/-! ## 第0Witt係数が正則な商のtilt射影核

kでd₀が非零因子という仮定を明示する。一般のpねじれを持つWitt商へ
この仮定を無条件に適用しない。互換商の列は共通PerfectionPrincipalKernelを使う。
-/

@[expose] public noncomputable section WittQuotientTiltKernelRegular

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- d₀が正則なら、tilt核候補の正の座標の零化元はFrobeniusで消える。 -/
theorem wittQuotientTilt_annihilator_pow_eq_zero
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) (n : ℕ)
    (z : ModP (WittVector p k ⧸ Ideal.span {d}) p)
    (hz : PreTilt.coeff (n + 1) (wittQuotientTiltMap p k d (d.coeff 0)) * z = 0) :
    z ^ p = 0 := by
  let e := wittQuotientModPEquiv p k d
  let q := Ideal.Quotient.mk (Ideal.span {d.coeff 0})
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n + 1] (d.coeff 0)
  let N := p ^ (n + 1)
  have he (x : k) : e (wittQuotientCoefficientMap p k d x) = q x := by
    change e (e.symm (q x)) = q x
    exact e.apply_symm_apply _
  have ha : a ^ N = d.coeff 0 := iterate_frobeniusEquiv_symm_pow_p_pow k p _ (n + 1)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN : 2 ≤ N := by
    exact hp2.trans (Nat.le_self_pow (by omega : n + 1 ≠ 0) p)
  have haReg : IsLeftRegular a :=
    (IsLeftRegular.pow_iff (by omega : 0 < N)).mp (by rw [ha]; exact hreg)
  obtain ⟨b, hb⟩ := wittQuotientCoefficientMap_surjective p k d z
  have hprod : a * b ∈ Ideal.span {d.coeff 0} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (a * b) = 0
    have h := congrArg e hz
    rw [wittQuotientTiltMap_coeff, ← hb] at h
    change e (wittQuotientCoefficientMap p k d a * wittQuotientCoefficientMap p k d b) = e 0 at h
    rw [map_mul, he, he, map_zero] at h
    simpa only [map_mul] using h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hprod
  have hN' : N - 1 + 1 = N := by omega
  have hb' : b = a ^ (N - 1) * c := by
    apply haReg
    change a * b = a * (a ^ (N - 1) * c)
    have hpow : a ^ N = a * a ^ (N - 1) := by
      calc
        a ^ N = a ^ (N - 1 + 1) := congrArg (fun m ↦ a ^ m) hN'.symm
        _ = a * a ^ (N - 1) := pow_succ' _ _
    rw [hc, ← ha, hpow, mul_assoc]
  have hle : N ≤ (N - 1) * p := by
    have h := Nat.mul_le_mul_left (N - 1) hp2
    omega
  have hbpow : b ^ p ∈ Ideal.span {d.coeff 0} := by
    rw [hb', mul_pow, ← pow_mul]
    apply (Ideal.span {d.coeff 0}).mul_mem_right
    apply (Ideal.span {d.coeff 0}).pow_mem_of_pow_mem (m := N) _ hle
    rw [ha]
    exact Ideal.subset_span (by simp)
  apply e.injective
  rw [map_pow, ← hb, he]
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hbpow, map_zero]

/-- d₀が正則なWitt商のtiltの第0射影核は、d₀の標準tilt像で生成される。 -/
theorem wittQuotientTilt_coeff_zero_kernel_eq_span
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt (WittVector p k ⧸ Ideal.span {d}) p →+*
      ModP (WittVector p k ⧸ Ideal.span {d}) p) =
        Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)} := by
  apply perfection_coeff_zero_kernel_eq_span
    (ModP (WittVector p k ⧸ Ideal.span {d}) p) p
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}))
    (wittQuotientTiltMap p k d (d.coeff 0)) (wittQuotientTiltMap_coeff_zero_d p k d)
  · intro z
    change z ^ p = 0 ↔ z ∈ Ideal.span {(PreTilt.coeff 1
      (wittQuotientTiltMap p k d (d.coeff 0)))}
    rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
    apply wittQuotientModP_pow_eq_zero_iff_mem_span
    exact frobeniusEquiv_symm_pow_p k p _
  · exact wittQuotientTilt_annihilator_pow_eq_zero p k d hreg

end SerrePositivity.BhattScholze

end WittQuotientTiltKernelRegular

/-! ## 完備な係数環からWitt商tiltへの全射性

F6の核計算と、tiltの座標からの分離性を使う。
Witt商のp正則性やFontaine核の単項性を仮定しない。
-/

@[expose] public noncomputable section WittQuotientTiltSurjective

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- d₀の標準tilt像のイデアル進分離性は、各座標の冪零性から従う。 -/
theorem wittQuotientTilt_image_isHausdorff :
    IsHausdorff (Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)})
      (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply Perfection.ext
  intro n
  let r := wittQuotientTiltMap p k d (d.coeff 0)
  have hm := hx (p ^ n)
  simp only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow] at hm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  change PreTilt.coeff n x = 0
  rw [hy, map_mul, map_pow]
  have he : PreTilt.coeff n r ^ (p ^ n) = PreTilt.coeff 0 r := by
    simpa only [zero_add] using compatibleRoots_pow p (fun i ↦ PreTilt.coeff i r)
      (fun i ↦ PreTilt.coeff_pow_p r i) 0 n
  rw [he, wittQuotientTiltMap_coeff_zero_d, zero_mul]

/-- 係数環がd₀進前完備なら標準tilt射は全射。一般の零因子d₀を許す。 -/
theorem wittQuotientTiltMap_surjective [IsPrecomplete (Ideal.span {d.coeff 0}) k] :
    Function.Surjective (wittQuotientTiltMap p k d) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let L := wittQuotientTiltMap p k d
  let I : Ideal k := Ideal.span {d.coeff 0}
  let K : Ideal (PreTilt S p) := Ideal.span {L (d.coeff 0)}
  have hmap : I.map L = K := by rw [Ideal.map_span, Set.image_singleton]
  let : IsHausdorff (I.map L) (PreTilt S p) := by
    rw [hmap]
    exact wittQuotientTilt_image_isHausdorff p k d
  apply surjective_of_mk_map_comp_surjective (I := I) L
  let q : PreTilt S p →+* ModP S p := PreTilt.coeff 0
  have hker : RingHom.ker q = K := wittQuotientTilt_coeff_zero_kernel_eq_span_general p k d
  have hq : Function.Surjective q := Perfection.coeff_surjective
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d})) 0
  let e : PreTilt S p ⧸ K ≃+* ModP S p :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
  have he (x : PreTilt S p) : e (Ideal.Quotient.mk K x) = q x := rfl
  rw [hmap]
  intro z
  obtain ⟨a, ha⟩ := wittQuotientCoefficientMap_surjective p k d (e z)
  refine ⟨a, e.injective ?_⟩
  change e (Ideal.Quotient.mk K (L a)) = e z
  rw [he]
  exact ha

end SerrePositivity.BhattScholze

end WittQuotientTiltSurjective
