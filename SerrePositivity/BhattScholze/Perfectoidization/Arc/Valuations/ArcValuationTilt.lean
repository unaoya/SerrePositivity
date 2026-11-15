module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcPerfectoidBase
public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.KrullDimension.LocalRing

/-!
# 階数 1 の付値環の tilt

## 概要
p 完備な階数 1 の整 perfectoid 付値環の tilt は完全な階数 1 の付値環。

## 方針
sharp に両立する p 冪根を取って各成分で割り、可除性を tilt に戻す。
非単元の冪の可除性から階数を確認する。

## 規約
mod p が零環の場合、tilt は零環。

## 使われ方
BS 著者版 Proposition 8.10 の証明で、付値環による試験を tilt に移す。
-/

@[expose] public noncomputable section

universe u
open _root_.CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime]

/-- 逆極限の底の mod p が零環なら、tilt も零環。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRing (O : Type u) [CommRing O] : CommRingCat.{u} := by
  classical
  exact if h : IsUnit (p : O) then CommRingCat.of (ULift.{u} (ZMod 1))
    else
      letI : Fact (¬ IsUnit (p : O)) := ⟨h⟩
      CommRingCat.of (PreTilt O p)

/-- mod p が非零の場合の tilt と Mathlib の逆極限の比較。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRingEquivPreTilt (O : Type u) [CommRing O] [Fact (¬ IsUnit (p : O))] :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRing p O : Type u) ≃+* PreTilt O p := by
  classical
  let h : ¬ IsUnit (p : O) := Fact.out
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRing
  rw [dite_eq_right h]

section PreTiltValuation

variable {W : Type u} [CommRing W] [Fact (¬ IsUnit (p : W))]
  [IsAdicComplete (Ideal.span {(p : W)}) W]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt (x : PreTilt W p) (n : ℕ) : W :=
  (((frobeniusEquiv (PreTilt W p) p).symm^[n]) x).untilt

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_pow (x : PreTilt W p) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n ^ (p ^ n) = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_step (x : PreTilt W p) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt
  rw [Function.iterate_succ_apply', ← map_pow]
  congr 1
  exact (frobeniusEquiv (PreTilt W p) p).apply_symm_apply _

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_modP (x : PreTilt W p) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : W)}) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n) = PreTilt.coeff n x := by
  simp [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_zero : (0 : PreTilt W p).untilt = 0 :=
  Perfection.teichmuller_zero

variable [IsDomain W]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_eq_zero {x : PreTilt W p} : x.untilt = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun h => h.symm ▸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_zero p⟩
  apply Perfection.ext
  intro n
  have h := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_pow p x n).trans hx
  have hn := eq_zero_of_pow_eq_zero h
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, ← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_modP p x n, hn, map_zero, map_zero]

variable [ValuationRing W]

/-- 可除性は tilt と sharp の間で一致する。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_dvd_iff_sharp_dvd {x y : PreTilt W p} : x ∣ y ↔ x.untilt ∣ y.untilt := by
  refine ⟨map_dvd PreTilt.untilt, ?_⟩
  intro h
  by_cases hy : y = 0
  · rw [hy]; exact dvd_zero _
  have hy0 : y.untilt ≠ 0 := fun h => hy ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_eq_zero p).mp h)
  have hx0 : x.untilt ≠ 0 := fun hx => hy0 (zero_dvd_iff.mp (hx ▸ h))
  have hxAt (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n ≠ 0 := fun hz =>
    hx0 (by rw [← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_pow p x n, hz, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hd (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n ∣ _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p y n := by
    rcases ValuationRing.dvd_total (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p y n) with hxy | ⟨c, hc⟩
    · exact hxy
    obtain ⟨d, hd⟩ := h
    have hs : x.untilt = y.untilt * c ^ (p ^ n) := by
      rw [← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_pow p x n, hc, mul_pow, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_pow]
    have hmul : y.untilt * 1 = y.untilt * (c ^ (p ^ n) * d) := by
      calc
        y.untilt * 1 = y.untilt := mul_one _
        _ = x.untilt * d := hd
        _ = y.untilt * (c ^ (p ^ n) * d) := by rw [hs, mul_assoc]
    have hu : IsUnit c := (isUnit_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
      (isUnit_iff_dvd_one.mpr ⟨d, mul_left_cancel₀ hy0 hmul⟩)
    rw [hc]
    exact (associated_mul_unit_right _ _ hu).dvd'
  choose c hc using hd
  have hstep (n : ℕ) : c (n + 1) ^ p = c n := by
    apply mul_left_cancel₀ (hxAt n)
    have h := congrArg (fun a : W => a ^ p) (hc (n + 1))
    rw [mul_pow, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_step, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_step] at h
    exact h.symm.trans (hc n)
  let q := Ideal.Quotient.mk (Ideal.span {(p : W)})
  let z : PreTilt W p := ⟨fun n => q (c n), fun n => by rw [← map_pow, hstep]⟩
  refine ⟨z, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n y = PreTilt.coeff n (x * z)
  rw [map_mul, ← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_modP p y n, ← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt_modP p x n]
  change q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p y n) = q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharpAt p x n) * q (c n)
  rw [hc, map_mul]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_isUnit_iff (x : PreTilt W p) : IsUnit x.untilt ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, isUnit_iff_dvd_one]
  simpa only [map_one] using (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_dvd_iff_sharp_dvd p (x := x) (y := 1)).symm

omit [ValuationRing W] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_isDomain : IsDomain (PreTilt W p) := by
  let : NoZeroDivisors (PreTilt W p) := ⟨fun {x y} hxy => by
    have h : x.untilt * y.untilt = 0 := by rw [← map_mul, hxy, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_zero]
    exact (mul_eq_zero.mp h).imp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_eq_zero p).mp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_eq_zero p).mp⟩
  let : Nontrivial (PreTilt W p) := ⟨⟨1, 0, fun h => by
    have hh := congrArg (PreTilt.untilt (p := p) (O := W)) h
    rw [map_one, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_zero] at hh
    exact one_ne_zero hh⟩⟩
  exact NoZeroDivisors.to_isDomain _

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_valuationRing [IsDomain (PreTilt W p)] : ValuationRing (PreTilt W p) :=
  ValuationRing.iff_dvd_total.mpr ⟨fun x y =>
    (ValuationRing.dvd_total x.untilt y.untilt).imp
      (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_dvd_iff_sharp_dvd p).mpr (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_dvd_iff_sharp_dvd p).mpr⟩

omit [IsAdicComplete (Ideal.span {(p : W)}) W] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_nonzero_nonunit_modP (hW : ringKrullDim W = 1)
    (hF : ∃ (π : W) (u : Wˣ), (p : W) = u * π ^ p) :
    ∃ r : ModP W p, r ≠ 0 ∧ ¬ IsUnit r := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : W)})
  have hlocal : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  suffices ∃ a : W, ¬ (p : W) ∣ a ∧ ¬ IsUnit a by
    obtain ⟨a, ha, hu⟩ := this
    refine ⟨q a, ?_, fun h => hu (IsUnit.of_map q a h)⟩
    intro h
    exact ha (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h))
  by_cases hp : (p : W) = 0
  · obtain ⟨a, ha⟩ : ∃ a : W, a ≠ 0 ∧ ¬ IsUnit a := by
      by_contra! h
      apply (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hW).1
      exact ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => by
        obtain ⟨b, hb⟩ := isUnit_iff_dvd_one.mp (h x hx)
        exact ⟨b, hb.symm⟩⟩
    exact ⟨a, by simpa only [hp, zero_dvd_iff] using ha.1, ha.2⟩
  obtain ⟨π, u, hu⟩ := hF
  have hπ0 : π ≠ 0 := fun h => hp (by rw [hu, h, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero])
  have hπu : ¬ IsUnit π := fun h =>
    (Fact.out : ¬ IsUnit (p : W)) (hu ▸ u.isUnit.mul (h.pow p))
  refine ⟨π, fun h => ?_, hπu⟩
  have h' : π ^ p ∣ (p : W) := ⟨u, by rw [hu, mul_comm]⟩
  have h'' : π ^ p ∣ π ^ 1 := by simpa only [pow_one] using h'.trans h
  exact (not_le_of_gt (Fact.out : p.Prime).one_lt) ((pow_dvd_pow_iff hπ0 hπu).mp h'')

omit [IsAdicComplete (Ideal.span {(p : W)}) W] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_ringKrullDim_eq_one [IsDomain (PreTilt W p)] [ValuationRing (PreTilt W p)]
    (hW : ringKrullDim W = 1) (hperf : _root_.SerrePositivity.IsIntegralPerfectoid W p) :
    ringKrullDim (PreTilt W p) = 1 := by
  obtain hsub | ⟨_, _, hπ, hF, _⟩ := hperf
  · exact (hsub.elim 0 1 |> zero_ne_one).elim
  obtain ⟨r, hr0, hru⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_nonzero_nonunit_modP p hW hπ
  obtain ⟨x, hx⟩ := Perfection.coeff_surjective (p := p) hF 0 r
  have hx' : PreTilt.coeff 0 x = r := hx
  have hx0 : (x : PreTilt W p) ≠ 0 := by
    intro h
    change x = (0 : Perfection (ModP W p) p) at h
    exact hr0 (hx.symm.trans (h.symm ▸ map_zero (Perfection.coeff (ModP W p) p 0)))
  have hxu : ¬ IsUnit x := fun h => hru (hx' ▸ h.map (PreTilt.coeff 0))
  apply ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
  refine ⟨fun h => ?_, fun b hb a ha => ?_⟩
  · obtain ⟨b, hb⟩ := h.mul_inv_cancel hx0
    exact hxu (isUnit_iff_dvd_one.mpr ⟨b, hb.symm⟩)
  · have hanu : ¬ IsUnit a.untilt :=
      fun h => (IsLocalRing.mem_maximalIdeal a).mp ha ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_isUnit_iff p a).mp h)
    have hb0 : b.untilt ≠ 0 := fun h => hb ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.sharp_eq_zero p).mp h)
    obtain ⟨n, hn⟩ := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hW).2 b.untilt hb0
      ((IsLocalRing.mem_maximalIdeal a.untilt).mpr hanu)
    refine ⟨n, Ideal.mem_span_singleton.mpr ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_dvd_iff_sharp_dvd p).mpr ?_)⟩
    rw [map_pow]
    exact Ideal.mem_span_singleton.mp hn


end PreTiltValuation

/-- p 完備な階数 1 の perfectoid 付値環の tilt も階数 1 の付値環。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tilt_rankOneValuationRing (W : Type u) [CommRing W]
    (hW : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.IsRankOneCompleteValuationRing p W) (hperf : _root_.SerrePositivity.IsIntegralPerfectoid W p) :
    let V := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRing p W : Type u)
    ∃ hV : IsDomain V, @ValuationRing V _ hV ∧ ringKrullDim V = 1 ∧
      CharP V p ∧ PerfectRing V p := by
  let := hW.isDomain
  let := hW.valuationRing
  let := hW.adicComplete
  have hp : ¬ IsUnit (p : W) := by
    intro hu
    have htop : IsAdicComplete (⊤ : Ideal W) W :=
      Ideal.span_singleton_eq_top.mpr hu ▸ hW.adicComplete
    exact zero_ne_one (htop.subsingleton.elim 0 1)
  let : Fact (¬ IsUnit (p : W)) := ⟨hp⟩
  let V := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRing p W : Type u)
  let e : V ≃+* PreTilt W p := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tiltRingEquivPreTilt p W
  let := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_isDomain (W := W) p
  let := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_valuationRing (W := W) p
  let hV : IsDomain V := e.injective.isDomain e.toRingHom
  let hVal : ValuationRing V := ValuationRing.iff_dvd_total.mpr ⟨fun x y => by
    rcases ValuationRing.dvd_total (e x) (e y) with h | h
    · exact Or.inl (by simpa only [RingEquiv.symm_apply_apply] using map_dvd e.symm h)
    · exact Or.inr (by simpa only [RingEquiv.symm_apply_apply] using map_dvd e.symm h)⟩
  let hchar : CharP V p := charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  refine ⟨hV, hVal, e.ringKrullDim.trans (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.preTilt_ringKrullDim_eq_one p hW.krullDim_eq_one hperf),
    hchar, ⟨?_⟩⟩
  have hpow : (fun x : V => x ^ p) = e.symm ∘ (fun x : PreTilt W p => x ^ p) ∘ e := by
    funext x
    simp only [Function.comp_apply, ← map_pow, RingEquiv.symm_apply_apply]
  rw [hpow]
  exact e.symm.bijective.comp (PerfectRing.bijective_frobenius.comp e.bijective)


end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 8.10" (partial := component) "BM18 の経路 B（BS-W12）の B1〜B5 は本体。組み立て B6 は ⑥ の BS17 Thm 4.1 (i) 待ち ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tilt_rankOneValuationRing
