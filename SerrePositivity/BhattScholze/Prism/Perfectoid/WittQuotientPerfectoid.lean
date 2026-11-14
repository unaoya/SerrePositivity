module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTilt
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import SerrePositivity.CommutativeAlgebra.Adic.BoundedTorsionQuotient
public import Mathlib.RingTheory.AdicCompletion.Topology
public import SerrePositivity.CommutativeAlgebra.Witt.Lift

/-!
# 完備な distinguished Witt 商は perfectoid（BS 著者版 Theorem 3.10 の計算）

## 概要
W(k)/(d) の標準 Fontaine 比較写像、その単射性と同型条件、tilt 同型、完備な distinguished Witt 商の perfectoid 性と Fontaine 核の生成元。

## 方針
Fontaine 比較射の全単射性から核を移す。第 0 係数が正則な場合を経由して一般の場合へ。

## 規約
F7（Fontaine 核進分離性）を仮定しない。

## 使われ方
完全 prism の商の perfectoid 性（Prism/Perfectoid/PerfectPrismPerfectoid）。
-/

universe u

/-! ## Witt商の標準Fontaine比較写像

BS 著者版 Theorem 3.10の比較に使う具体的なδ射と商上の同型。
商の古典的p進完備性は仮定し、台Witt環の同型とは区別する。
-/

@[expose] public noncomputable section WittQuotientFontaineComparison

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 標準tilt射が誘導するWitt環からFontaine環への具体的な比較射。 -/
def wittQuotientFontaineMap :
    WittVector p k →+* WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) :=
  WittVector.map (wittQuotientTiltMap p k d)

/-- 標準Fontaine比較射は標準δ構造と可換する。 -/
theorem wittQuotientFontaineMap_isDeltaHom :
    (wittDeltaStructure p k).IsDeltaHom
      (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))
      (wittQuotientFontaineMap p k d) :=
  wittDeltaStructure_map_isDeltaHom p k (wittQuotientTiltMap p k d)

/-- 比較射でdistinguished元dの像もdistinguished。 -/
theorem wittQuotientFontaineMap_isDistinguished
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)).IsDistinguished
      (wittQuotientFontaineMap p k d d) :=
  (wittQuotientFontaineMap_isDeltaHom p k d).map_isDistinguished hd

variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- Fontaine射と標準Witt比較射の合成は、元の標準商射と一致する。
各p冪商でTeichmüller元の一致を使い、古典的p進分離性で結論する。 -/
theorem wittQuotientFontaineMap_comp_fontaineTheta :
    (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p).comp
      (wittQuotientFontaineMap p k d) = Ideal.Quotient.mk (Ideal.span {d}) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let f := (WittVector.fontaineTheta S p).comp (wittQuotientFontaineMap p k d)
  let g := Ideal.Quotient.mk (Ideal.span {d})
  have ht (x : k) : f (WittVector.teichmuller p x) = g (WittVector.teichmuller p x) := by
    change WittVector.fontaineTheta S p
      (WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p x)) = _
    rw [WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller,
      wittQuotientTiltMap_untilt]
  apply RingHom.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : S)})).mpr
  intro n
  let q := Ideal.Quotient.mk (Ideal.span {(p : S)} ^ n)
  have hn : IsNilpotent (p : S ⧸ Ideal.span {(p : S)} ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast q p, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n)
  have hfg : q.comp f = q.comp g :=
    WittVector.eq_of_apply_teichmuller_eq _ _ hn (fun a ↦ congrArg q (ht a))
  rw [smul_eq_mul, Ideal.mul_top]
  apply SModEq.sub_mem.mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (f x - g x) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (RingHom.congr_fun hfg x)

/-- 標準Fontaine核の比較射による逆像は、元の(d)そのもの。 -/
theorem wittQuotientFontaineMap_comap_kernel :
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)).comap
      (wittQuotientFontaineMap p k d) = Ideal.span {d} := by
  change RingHom.ker ((WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p).comp
    (wittQuotientFontaineMap p k d)) = Ideal.span {d}
  rw [wittQuotientFontaineMap_comp_fontaineTheta]
  exact Ideal.mk_ker

/-- 比較射はdを標準Fontaine核へ送る。 -/
theorem wittQuotientFontaineMap_generator_mem_kernel :
    wittQuotientFontaineMap p k d d ∈
      RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) := by
  have h := wittQuotientFontaineMap_comap_kernel p k d
  exact (show d ∈ (RingHom.ker (WittVector.fontaineTheta
    (WittVector p k ⧸ Ideal.span {d}) p)).comap (wittQuotientFontaineMap p k d) by
      rw [h]; exact Ideal.subset_span (Set.mem_singleton _))

/-- 比較射が誘導する具体的な商環の射。 -/
def wittQuotientFontaineQuotientMap :
    (WittVector p k ⧸ Ideal.span {d}) →+*
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ⧸
        RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)) :=
  Ideal.quotientMap _ (wittQuotientFontaineMap p k d)
    (by rw [wittQuotientFontaineMap_comap_kernel])

/-- 比較射の誘導商射は代表元に比較射を適用する。 -/
@[simp] theorem wittQuotientFontaineQuotientMap_mk (x : WittVector p k) :
    wittQuotientFontaineQuotientMap p k d (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk _ (wittQuotientFontaineMap p k d x) := rfl

/-- 標準商射に対するFontaine第一同型の逆は、比較射の誘導商射に等しい。
全射性は商mod pのFrobenius全射性と古典的p完備性から供給する。 -/
theorem wittQuotientFontaineQuotientMap_eq_inverse :
    wittQuotientFontaineQuotientMap p k d =
      (RingHom.quotientKerEquivOfSurjective
        (surjective_fontaineTheta
          ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective
            (Ideal.span {d})))).symm.toRingHom := by
  let θ := WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p
  have hθ : Function.Surjective θ := surjective_fontaineTheta
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}))
  let e := RingHom.quotientKerEquivOfSurjective hθ
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply e.injective
  change e (Ideal.Quotient.mk (RingHom.ker θ) (wittQuotientFontaineMap p k d a)) =
    e (e.symm (Ideal.Quotient.mk (Ideal.span {d}) a))
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk, e.apply_symm_apply]
  exact RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p k d) a

/-- 標準比較射の誘導商射は全単射。台Witt環の全単射性は追加結論しない。 -/
theorem wittQuotientFontaineQuotientMap_bijective :
    Function.Bijective (wittQuotientFontaineQuotientMap p k d) := by
  rw [wittQuotientFontaineQuotientMap_eq_inverse]
  exact RingEquiv.bijective _

/-- 元のWitt商と標準Fontaine核による商の具体的な同型。 -/
def wittQuotientFontaineQuotientEquiv :
    (WittVector p k ⧸ Ideal.span {d}) ≃+*
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ⧸
        RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)) :=
  RingEquiv.ofBijective (wittQuotientFontaineQuotientMap p k d)
    (wittQuotientFontaineQuotientMap_bijective p k d)

/-- 構成した商同型の台環射は標準比較射の誘導商射。 -/
@[simp] theorem wittQuotientFontaineQuotientEquiv_toRingHom :
    (wittQuotientFontaineQuotientEquiv p k d).toRingHom =
      wittQuotientFontaineQuotientMap p k d := rfl

end SerrePositivity.BhattScholze

end WittQuotientFontaineComparison

/-! ## 第0係数が正則なdistinguished Witt商のperfectoid性

既存のIsIntegralPerfectoidとFontaine核判定を使う具体的な定理。
商の古典的p完備性は明示的な仮定。一般のpねじれ商やWitt復元はまだ含めない。
-/

@[expose] public noncomputable section WittRegularQuotientPerfectoid

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- d₀が正則ならW(k)/(d)ではpが正則。既存の正則商APIにWitt剰余同型を供給する。 -/
theorem wittQuotient_p_mul_injective_of_coeff_zero_regular (d : WittVector p k)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Injective (fun x : WittVector p k ⧸ Ideal.span {d} ↦
      (p : WittVector p k ⧸ Ideal.span {d}) * x) := by
  have hp : IsSMulRegular (WittVector p k) (p : WittVector p k) :=
    (wittDeltaStructure_isPerfect p k).p_mul_injective
  have hd : IsSMulRegular (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) d) := by
    intro x y hxy
    let e := WittVector.quotientPEquiv (p := p) (k := k)
    apply e.injective
    apply hreg
    have h := congrArg e hxy
    change e (Ideal.Quotient.mk _ d * x) = e (Ideal.Quotient.mk _ d * y) at h
    rw [map_mul, map_mul] at h
    exact h
  exact isSMulRegular_quotient_span_of_regular_mod (WittVector p k) (p : WittVector p k) d hp hd

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 完備なdistinguished Witt商でd₀が正則なら、Fontaine核は単項。
既存引用への依存なしに、tilt核と単元係数の原始元から証明する。 -/
theorem wittRegularQuotient_fontaine_kernel_isPrincipal
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)).IsPrincipal := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let q := Ideal.Quotient.mk (Ideal.span {d})
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p k d hd
  obtain ⟨a, ha⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (d.coeff 0)
  change a ^ p = d.coeff 0 at ha
  let r := wittQuotientTiltMap p k d a
  let w := Units.map q.toMonoidHom u
  let v := -w⁻¹
  have hpEq : (p : S) = (v : S) * r.untilt ^ p := by
    have hq : q (WittVector.teichmuller p a) ^ p + (p : S) * (w : S) = 0 := by
      have h := congrArg q hu
      rw [map_add, map_mul, map_natCast] at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))] at h
      change 0 = q (WittVector.teichmuller p (d.coeff 0)) + (p : S) * q (u : WittVector p k) at h
      change q (WittVector.teichmuller p a) ^ p + (p : S) * q (u : WittVector p k) = 0
      rw [← map_pow, ← map_pow, ha]
      exact h.symm
    have hπ := eq_neg_of_add_eq_zero_left hq
    rw [wittQuotientTiltMap_untilt, hπ]
    simp [v, mul_comm, mul_assoc]
  have hF : Function.Surjective (frobenius (ModP S p) p) :=
    (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d})
  obtain ⟨b, hb⟩ := surjective_fontaineTheta hF (-(v : S))
  have hb0 : IsUnit (b.coeff 0) := by
    apply perfection_isUnit_of_coeff_zero (ModP S p) p
    change IsUnit (PreTilt.coeff 0 (b.coeff 0))
    rw [← WittVector.mk_fontaineTheta, hb]
    exact (v.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : S)}))
  have hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p r ^ p * b) = 0 := by
    rw [map_add, map_mul, map_pow, map_natCast, WittVector.fontaineTheta_teichmuller, hb, hpEq]
    ring
  have htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {r ^ p} := by
    rw [wittQuotientTilt_coeff_zero_kernel_eq_span p k d hreg]
    congr 1
    change {wittQuotientTiltMap p k d (d.coeff 0)} = {wittQuotientTiltMap p k d a ^ p}
    rw [← map_pow, ha]
  rw [PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_tilt_coeff_kernel S p
    (wittQuotient_p_mul_injective_of_coeff_zero_regular p k d hreg) r b hb0 hξ htilt]
  infer_instance

/-- 第0係数が正則なdistinguished Witt元の古典的p進完備商は整perfectoid。
定義の四条件を既存APIにより供給し、一般商の完備性を追加結論しない。 -/
theorem wittRegularQuotient_isIntegralPerfectoid
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p :=
  Or.inr ⟨Fact.out, inferInstance,
    witt_distinguished_quotient_exists_unit_mul_pow_p p k d hd,
    (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}),
    wittRegularQuotient_fontaine_kernel_isPrincipal p k d hd hreg⟩

end SerrePositivity.BhattScholze

end WittRegularQuotientPerfectoid

/-! ## 正則Witt商の標準比較射によるFontaine核の生成

存在だけでなく、元のdistinguished元dの標準Fontaine像が核を生成すると特定する。
商の古典的p完備性とd₀の正則性を明示したBS 著者版 Theorem 3.10の部分定理。
-/

@[expose] public noncomputable section WittRegularQuotientFontaineKernel

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- d₀が正則な完備distinguished Witt商の標準Fontaine核は、比較射のd像で生成される。 -/
theorem wittRegularQuotient_fontaine_kernel_eq_span_image
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) =
      Ideal.span {wittQuotientFontaineMap p k d d} := by
  apply PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_firstCoeff_unit
    (WittVector p k ⧸ Ideal.span {d}) p
    (wittRegularQuotient_fontaine_kernel_isPrincipal p k d hd hreg)
    (wittQuotientFontaineMap p k d d)
    (wittQuotientFontaineMap_generator_mem_kernel p k d)
  have hu : IsUnit ((wittQuotientFontaineMap p k d d).coeff 1) :=
    (wittDeltaStructure_isDistinguished_iff p
      (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) _).mp
        (wittQuotientFontaineMap_isDistinguished p k d hd)
  exact hu.map (PreTilt.coeff 0)

/-- 正則distinguished元の生成イデアルの標準Fontaine像は標準Fontaine核全体。 -/
theorem wittRegularQuotient_map_span_eq_fontaine_kernel
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (Ideal.span {d}).map (wittQuotientFontaineMap p k d) =
      RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) := by
  rw [Ideal.map_span, Set.image_singleton,
    wittRegularQuotient_fontaine_kernel_eq_span_image p k d hd hreg]

end SerrePositivity.BhattScholze

end WittRegularQuotientFontaineKernel

/-! ## Witt商の標準Fontaine比較射の単射性と同型条件

BS 著者版 Theorem 3.10の台環比較に向けた具体的な定理。
源のd進分離性で単射性を証明し、全射性には標的の核進分離性を明示する。
その分離性自体や一般Witt復元を未証明入力で置き換えない。
-/

@[expose] public noncomputable section WittQuotientFontaineIso

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- distinguished元の標準Fontaine像は、完全Witt環で非零因子。
源のd₀正則性・d進完備性や商のp完備性は不要。 -/
theorem wittQuotientFontaineMap_generator_mul_injective
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (fun x : WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ↦
      wittQuotientFontaineMap p k d d * x) := by
  have hperfect := wittDeltaStructure_isPerfect p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)
  exact hperfect.distinguished_mul_injective
    (wittQuotientFontaineMap_isDistinguished p k d hd)

variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 標準Fontaine比較射の核の元は、源の(d)のすべての冪に属する。 -/
theorem wittQuotientFontaineMap_kernel_mem_pow
    (hd : (wittDeltaStructure p k).IsDistinguished d) (n : ℕ) (x : WittVector p k)
    (hx : wittQuotientFontaineMap p k d x = 0) : x ∈ Ideal.span {d} ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hxI : x ∈ Ideal.span {d} := by
      rw [← wittQuotientFontaineMap_comap_kernel p k d]
      change WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p
        (wittQuotientFontaineMap p k d x) = 0
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxI
    have hyker : wittQuotientFontaineMap p k d y = 0 := by
      apply wittQuotientFontaineMap_generator_mul_injective p k d hd
      change wittQuotientFontaineMap p k d d * wittQuotientFontaineMap p k d y =
        wittQuotientFontaineMap p k d d * 0
      rw [mul_zero, ← map_mul, ← hy, hx]
    rw [hy, pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) (ih y hyker)

/-- 源がd進分離なら、distinguished商の標準Fontaine比較射は単射。
d₀の正則性は要求しない。 -/
theorem wittQuotientFontaineMap_injective
    [IsHausdorff (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (wittQuotientFontaineMap p k d) := by
  apply (injective_iff_map_eq_zero (wittQuotientFontaineMap p k d)).mpr
  intro x hx
  apply IsHausdorff.haus' (I := Ideal.span {d}) x
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero, smul_eq_mul, Ideal.mul_top] using
    wittQuotientFontaineMap_kernel_mem_pow p k d hd n x hx

/-- 同じ仮定のもとで標準tilt射も単射。Teichmüller元でWitt比較射の単射性を使う。 -/
theorem wittQuotientTiltMap_injective
    [IsHausdorff (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (wittQuotientTiltMap p k d) := by
  intro x y hxy
  have h : WittVector.teichmuller p x = WittVector.teichmuller p y := by
    apply wittQuotientFontaineMap_injective p k d hd
    change WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p x) =
      WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p y)
    rw [WittVector.map_teichmuller, WittVector.map_teichmuller, hxy]
  simpa only [WittVector.teichmuller_coeff_zero] using congrArg (fun z ↦ z.coeff 0) h

/-- 正則d₀の商では、源のd進前完備性と標的のFontaine核進分離性から比較射は全射。
核進分離性は明示的な仮定であり、perfectoid性だけから自動的に供給しない。 -/
theorem wittRegularQuotientFontaineMap_surjective
    [IsPrecomplete (Ideal.span {d}) (WittVector p k)]
    [IsHausdorff (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Surjective (wittQuotientFontaineMap p k d) := by
  have heq := wittRegularQuotient_map_span_eq_fontaine_kernel p k d hd hreg
  let : IsHausdorff ((Ideal.span {d}).map (wittQuotientFontaineMap p k d))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)) := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := Ideal.span {d})
    (wittQuotientFontaineMap p k d)
  rw [heq]
  change Function.Surjective ((wittQuotientFontaineQuotientMap p k d).comp
    (Ideal.Quotient.mk (Ideal.span {d})))
  exact (wittQuotientFontaineQuotientMap_bijective p k d).2.comp Ideal.Quotient.mk_surjective

/-- 明示した二つのadic条件を持つ正則distinguished Witt商の標準比較射は全単射。 -/
theorem wittRegularQuotientFontaineMap_bijective
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
    [IsHausdorff (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Bijective (wittQuotientFontaineMap p k d) :=
  ⟨wittQuotientFontaineMap_injective p k d hd,
    wittRegularQuotientFontaineMap_surjective p k d hd hreg⟩

variable [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
variable [IsHausdorff
  (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
  (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]

/-- 明示したadic条件のもとで構成する、元のWitt環とFontaine環の具体的な同型。 -/
def wittRegularQuotientFontaineEquiv
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    WittVector p k ≃+* WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) :=
  RingEquiv.ofBijective (wittQuotientFontaineMap p k d)
    (wittRegularQuotientFontaineMap_bijective p k d hd hreg)

/-- 同型の台環射は既に構成した標準Fontaine比較射。 -/
@[simp] theorem wittRegularQuotientFontaineEquiv_toRingHom
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (wittRegularQuotientFontaineEquiv p k d hd hreg).toRingHom =
      wittQuotientFontaineMap p k d := rfl

/-- 構成した同型の逆も標準Witt δ構造を保存する。 -/
theorem wittRegularQuotientFontaineEquiv_symm_isDeltaHom
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)).IsDeltaHom
      (wittDeltaStructure p k)
      (wittRegularQuotientFontaineEquiv p k d hd hreg).symm.toRingHom :=
  DeltaStructure.IsDeltaHom.symm (wittQuotientFontaineMap_isDeltaHom p k d)

/-- 逆比較射と元の標準商射の合成は、標準Fontaine射と一致する。 -/
theorem wittRegularQuotientFontaineEquiv_symm_comp_quotient
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (Ideal.Quotient.mk (Ideal.span {d})).comp
      (wittRegularQuotientFontaineEquiv p k d hd hreg).symm.toRingHom =
      WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p := by
  let e := wittRegularQuotientFontaineEquiv p k d hd hreg
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  change Ideal.Quotient.mk (Ideal.span {d}) (e.symm (e y)) =
    WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p (e y)
  rw [e.symm_apply_apply]
  exact (RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p k d) y).symm

end SerrePositivity.BhattScholze

end WittQuotientFontaineIso

/-! ## 完全prismのWitt表示における一般商のtilt同型

W(k)のd完備性からkのd₀完備性をF5で供給し、F6による全射性と既存の単射性を合成する。
商のp正則性・d₀正則性・Fontaine核進分離性は要求しない。
-/

@[expose] public noncomputable section WittQuotientTiltEquiv

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt環がd進完備なら、係数環はd₀進完備。mod pの被約性から有界ねじれを供給する。 -/
theorem witt_coeff_zero_isAdicComplete (d : WittVector p k)
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)] :
    IsAdicComplete (Ideal.span {d.coeff 0}) k := by
  let M := WittVector p k ⧸ Ideal.span {(p : WittVector p k)}
  let e : M ≃+* k := WittVector.quotientPEquiv
  let q := Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)})
  let : IsReduced k := isReduced_of_perfectPower k p (Fact.out : p.Prime).one_lt
  let : IsReduced M := isReduced_of_injective e.toRingHom e.injective
  have hb : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, q d ^ n * x = 0 → q d ^ N * x = 0 := by
    refine ⟨1, ?_⟩
    intro n x hx
    rw [pow_one]
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, one_mul] at hx
      rw [hx, mul_zero]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      apply eq_zero_of_pow_eq_zero (n := m + 1)
      rw [mul_pow, pow_succ' x m, ← mul_assoc, hx, zero_mul]
  have hM := isAdicComplete_principal_quotient_of_bounded_torsion (WittVector p k) d
    (p : WittVector p k) hb
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {q d}) e).mpr hM
  have he : e (q d) = d.coeff 0 := rfl
  simpa only [Ideal.map_span, Set.image_singleton, he] using h

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 完備なdistinguished Witt商の標準tilt射は全単射。d₀正則性を追加しない。 -/
theorem wittQuotientTiltMap_bijective (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Bijective (wittQuotientTiltMap p k d) := by
  let := witt_coeff_zero_isAdicComplete p k d
  exact ⟨wittQuotientTiltMap_injective p k d hd, wittQuotientTiltMap_surjective p k d⟩

/-- 標準tilt射を環同型として束ねる。 -/
def wittQuotientTiltEquiv (hd : (wittDeltaStructure p k).IsDistinguished d) :
    k ≃+* PreTilt (WittVector p k ⧸ Ideal.span {d}) p :=
  RingEquiv.ofBijective (wittQuotientTiltMap p k d) (wittQuotientTiltMap_bijective p k d hd)

end SerrePositivity.BhattScholze

end WittQuotientTiltEquiv

/-! ## 完備なdistinguished Witt商の一般perfectoid性

F4/F5/F6の接続。標準Fontaine比較射の全単射性から核を直接移す。
商のp正則性・第0係数の正則性・F7の核進分離性を仮定しない。
-/

@[expose] public noncomputable section WittCompleteQuotientPerfectoid

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [IsAdicComplete (Ideal.span {d}) (WittVector p k)]

section Nonunit
variable [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 一般の完備distinguished Witt商の標準Fontaine比較射は全単射。 -/
theorem wittCompleteQuotientFontaineMap_bijective
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Bijective (wittQuotientFontaineMap p k d) := by
  have h := wittQuotientTiltMap_bijective p k d hd
  exact ⟨WittVector.map_injective _ h.1, WittVector.map_surjective _ h.2⟩

/-- 一般商のFontaine核は、具体的な標準比較射によるdの像で生成される。 -/
theorem wittCompleteQuotient_fontaine_kernel_eq_span
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) =
      Ideal.span {wittQuotientFontaineMap p k d d} := by
  have h := Ideal.map_comap_of_surjective (wittQuotientFontaineMap p k d)
    (wittCompleteQuotientFontaineMap_bijective p k d hd).2
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
  rw [wittQuotientFontaineMap_comap_kernel p k d, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end Nonunit

/-- d進完備なWitt環のdistinguished商は、一般のpねじれを許して整perfectoid。零環も含む。 -/
theorem wittCompleteDistinguishedQuotient_isIntegralPerfectoid
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p := by
  let S := WittVector p k ⧸ Ideal.span {d}
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact Or.inl hs
  · let := hn
    let : IsAdicComplete (Ideal.span {(p : S)}) S :=
      (wittDeltaStructure_isPerfect p k).distinguished_quotient_isAdicComplete hd
    have hp : ¬ IsUnit (p : S) := by
      intro hu
      let : Subsingleton S := subsingleton_of_isUnit_natCast_of_isHausdorff p S hu
      exact zero_ne_one (Subsingleton.elim (0 : S) 1)
    let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    refine Or.inr ⟨hp, inferInstance,
      witt_distinguished_quotient_exists_unit_mul_pow_p p k d hd,
      (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}), ?_⟩
    rw [wittCompleteQuotient_fontaine_kernel_eq_span p k d hd]
    infer_instance

end SerrePositivity.BhattScholze

end WittCompleteQuotientPerfectoid
