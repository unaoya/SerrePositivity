module

public import SerrePositivity.CommutativeAlgebra.RegularSequencePowers
public import SerrePositivity.CommutativeAlgebra.FiniteLength

/-! # 正則列の冪で割った加群の長さ

正則なスカラーの積で割った商の短完全列から長さを計算する。
重複度の公式は使わない。
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open scoped Pointwise
open Submodule RingTheory.Sequence

variable {R : Type*} [CommRing R]

/-- `y` が `M` 上正則なら `M/xyM` の長さは `M/xM` と `M/yM` の長さの和。 -/
theorem length_quotSMulTop_mul (M : Type*) [AddCommGroup M] [Module R M]
    (x y : R) (hy : IsSMulRegular M y) :
    Module.length R (QuotSMulTop (x * y) M) =
      Module.length R (QuotSMulTop x M) + Module.length R (QuotSMulTop y M) := by
  let X : Submodule R M := x • ⊤
  let Y : Submodule R M := y • ⊤
  let J : Submodule R M := (x * y) • ⊤
  have hJY : J ≤ Y := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := (mem_smul_pointwise_iff_exists a (x * y) ⊤).mp ha
    exact (mem_smul_pointwise_iff_exists _ y ⊤).mpr
      ⟨x • b, trivial, by rw [mul_comm x y, mul_smul]⟩
  let m : M →ₗ[R] M ⧸ J := J.mkQ.comp (LinearMap.lsmul R M y)
  have hm : X ≤ LinearMap.ker m := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := (mem_smul_pointwise_iff_exists a x ⊤).mp ha
    apply (Submodule.Quotient.mk_eq_zero J).mpr
    exact (mem_smul_pointwise_iff_exists _ (x * y) ⊤).mpr
      ⟨b, trivial, by rw [mul_comm x y, mul_smul]; rfl⟩
  let f : M ⧸ X →ₗ[R] M ⧸ J := X.liftQ m hm
  let g : M ⧸ J →ₗ[R] M ⧸ Y := Submodule.factor hJY
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro a ha
    obtain ⟨a, rfl⟩ := X.mkQ_surjective a
    have ha' : y • a ∈ J := (Submodule.Quotient.mk_eq_zero J).mp ha
    obtain ⟨b, _, hb⟩ := (mem_smul_pointwise_iff_exists _ (x * y) ⊤).mp ha'
    have hb' : x • b = a := hy (by rwa [mul_comm x y, mul_smul] at hb)
    exact (Submodule.Quotient.mk_eq_zero X).mpr
      ((mem_smul_pointwise_iff_exists a x ⊤).mpr ⟨b, trivial, hb'⟩)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := Y.mkQ_surjective a
    exact ⟨J.mkQ a, rfl⟩
  have he : Function.Exact f g := by
    intro a
    obtain ⟨a, rfl⟩ := J.mkQ_surjective a
    constructor
    · intro ha
      obtain ⟨b, _, hb⟩ := (mem_smul_pointwise_iff_exists a y ⊤).mp
        ((Submodule.Quotient.mk_eq_zero Y).mp ha)
      exact ⟨X.mkQ b, congrArg J.mkQ hb⟩
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := X.mkQ_surjective b
      rw [← hb]
      exact (Submodule.Quotient.mk_eq_zero Y).mpr
        ((mem_smul_pointwise_iff_exists _ y ⊤).mpr ⟨b, trivial, rfl⟩)
  exact Module.length_eq_add_of_exact f g hf hg he

/-- 正則なスカラーの `v` 乗で割った長さは `v` 倍。無限長も許す。 -/
theorem length_quotSMulTop_pow (M : Type*) [AddCommGroup M] [Module R M]
    (x : R) (hx : IsSMulRegular M x) (v : ℕ) :
    Module.length R (QuotSMulTop (x ^ v) M) =
      v * Module.length R (QuotSMulTop x M) := by
  induction v with
  | zero => simp [QuotSMulTop]
  | succ v ih =>
    rw [pow_succ, length_quotSMulTop_mul M (x ^ v) x hx, ih]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- 弱正則列の各元を `v` 乗すると、商の長さは `v^(列の長さ)` 倍。 -/
theorem length_quotient_regularSequence_powers [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {rs : List R} (h : IsWeaklyRegular M rs)
    (hm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) (v : ℕ) (hv : 0 < v) :
    Module.length R (M ⧸ (Ideal.ofList (rs.map (fun x ↦ x ^ v)) • ⊤ : Submodule R M)) =
      (v : ℕ∞) ^ rs.length *
        Module.length R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) := by
  induction rs generalizing M with
  | nil => rw [List.length_nil, pow_zero, one_mul]; rfl
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp h
    have hmrs : ∀ y ∈ rs, y ∈ IsLocalRing.maximalIdeal R :=
      fun y hy ↦ hm y (List.mem_cons_of_mem x hy)
    let ps := rs.map (fun y ↦ y ^ v)
    have hp : IsWeaklyRegular M (x :: ps) :=
      .cons hx (isWeaklyRegular_map_pow (QuotSMulTop x M) hrs hmrs v hv)
    have hmp : ∀ y ∈ x :: ps, y ∈ IsLocalRing.maximalIdeal R := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hm y (by simp)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact (IsLocalRing.maximalIdeal R).pow_mem_of_mem (hmrs a ha) v hv
    have hlast := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hp
      (by simpa using (List.perm_append_comm (l₁ := [x]) (l₂ := ps))) hmp
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hlast
    change Module.length R (M ⧸ (Ideal.ofList (x ^ v :: ps) • ⊤ : Submodule R M)) = _
    rw [(quotOfListConsSMulTopEquivQuotSMulTopOuter M (x ^ v) ps).length_eq,
      length_quotSMulTop_pow _ x hlast.2 v,
      ← (quotOfListConsSMulTopEquivQuotSMulTopOuter M x ps).length_eq,
      (quotOfListConsSMulTopEquivQuotSMulTopInner M x ps).length_eq,
      ih (QuotSMulTop x M) hrs hmrs,
      ← (quotOfListConsSMulTopEquivQuotSMulTopInner M x rs).length_eq]
    simp only [List.length_cons, pow_succ]
    ac_rfl

/-- `e` 個の正則な極大イデアル生成元の `v` 乗で割った長さは `v^e`。 -/
theorem length_quotient_parameter_powers [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : IsWeaklyRegular R (List.ofFn z)) (v : ℕ) (hv : 0 < v) :
    Module.length R (R ⧸ Ideal.span (Set.range fun j ↦ z j ^ v)) = (v : ℕ∞) ^ e := by
  have hm : ∀ x ∈ List.ofFn z, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rw [← hz]
    exact Ideal.subset_span (by simpa only [List.mem_ofFn, Set.mem_range] using hx)
  have h := length_quotient_regularSequence_powers R hreg hm v hv
  have hspan {n : ℕ} (w : Fin n → R) : Ideal.ofList (List.ofFn w) = Ideal.span (Set.range w) := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_ofFn
  have : IsSimpleModule R (R ⧸ Ideal.span (Set.range z)) :=
    isSimpleModule_quotient_span_of_eq hz
  change Module.length R (R ⧸ (Ideal.ofList ((List.ofFn z).map (fun x ↦ x ^ v)) * ⊤)) =
    (v : ℕ∞) ^ (List.ofFn z).length * Module.length R (R ⧸ (Ideal.ofList (List.ofFn z) * ⊤)) at h
  rw [List.map_ofFn, hspan, hspan, Ideal.mul_top, Ideal.mul_top] at h
  rw [show ((fun x : R ↦ x ^ v) ∘ z) = (fun j ↦ z j ^ v) from rfl] at h
  simpa only [List.length_ofFn, Module.length_eq_one, mul_one] using h

end SerrePositivity
