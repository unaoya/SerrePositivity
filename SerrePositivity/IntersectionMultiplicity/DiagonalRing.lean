module

public import SerrePositivity.CommutativeAlgebra.ParameterKoszulGrowth
public import SerrePositivity.CommutativeAlgebra.PowerSeriesRingHomExt
public import SerrePositivity.CommutativeAlgebra.PowerSeriesLocalStructure
public import SerrePositivity.CommutativeAlgebra.RegularParameters

/-! # 対角線の環 `R[[Y]]`

## 概要

`R = k[[X_1, …, X_d]]` に対し、`S = R[[Y_1, …, Y_d]]` を Serre の対角線論法の環として整備する。

- 定数 `C : R → S`（「`X` の側」）と、変数の取り替え `i₂ : R → S`、`X_i ↦ Y_i`（「`Y` の側」）。
  `S` の `R` 代数構造は `i₂` で与える。
- 評価 `Δ : S → R`、`Y_i ↦ X_i`。`Δ ∘ C = Δ ∘ i₂ = id`。
- 対角線の元 `δ_i = C(X_i) − Y_i`。`ker Δ = (δ)` で、`δ` は `S` の弱正則列。

## 方針

`S` には冪級数環の既定の `R` 代数構造（定数）があるので、型の別名 `DiagonalRing` を作り、
`R` 代数構造を `i₂` に取り替える。

- `Δ ∘ i₂ = id` は、冪級数環からの環準同型の一意性（`MvPowerSeries.ringHom_ext_of_isHausdorff`）による。
- `ker Δ ⊆ (δ)`：多項式 `p` については `p ≡ C(Δ p) mod (δ)`（多項式環からの環準同型の一意性）。
  一般の `f` は切り捨てとの差が `m_S^N` に入るので、`f − C(Δ f)` は全ての `N` で `(δ) + m_S^N` に入り、
  `S/(δ)` での Krull の交叉定理から `(δ)` に入る。
- `δ` の正則性：`m_S = (C(X), δ)` は `2d = dim S` 個の元で生成されるので、正則局所環の
  極小生成系として弱正則列になり、その前半の `δ` も弱正則列。

## 使われ方

`formalization-plans/serre-equal-characteristic.md` の K5・K6。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing MvPowerSeries

namespace SerrePositivity

variable (k : Type u) [Field k] (d : ℕ)

local notation "𝓡" => MvPowerSeries (Fin d) k

/-- 対角線の環 `R[[Y_1, …, Y_d]]`（`R = k[[X_1, …, X_d]]`）。`R` 代数構造は変数の取り替え
`X_i ↦ Y_i` で与えるので、冪級数環の既定の代数構造と区別するために別名にする。 -/
def DiagonalRing : Type u := MvPowerSeries (Fin d) (MvPowerSeries (Fin d) k)

namespace DiagonalRing

instance : CommRing (DiagonalRing k d) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin d) 𝓡))

instance : IsLocalRing (DiagonalRing k d) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries (Fin d) 𝓡))

instance : IsNoetherianRing (DiagonalRing k d) :=
  inferInstanceAs (IsNoetherianRing (MvPowerSeries (Fin d) 𝓡))

/-- 変数の取り替え `i₂ : R → S`、`X_i ↦ Y_i`。係数 `k` を定数として送る。 -/
instance : Algebra 𝓡 (DiagonalRing k d) :=
  (MvPowerSeries.map (MvPowerSeries.C (σ := Fin d) (R := k)) :
    𝓡 →+* MvPowerSeries (Fin d) 𝓡).toAlgebra

/-- 冪級数環としての見方（恒等写像）。 -/
def toPS : DiagonalRing k d ≃+* MvPowerSeries (Fin d) 𝓡 := RingEquiv.refl _

/-- 多項式の冪級数としての像。 -/
def ofPoly : MvPolynomial (Fin d) 𝓡 →+* DiagonalRing k d :=
  (toPS k d).symm.toRingHom.comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin d) (R := 𝓡))

/-- 定数 `C : R → S`（「`X` の側」）。 -/
def const : 𝓡 →+* DiagonalRing k d := MvPowerSeries.C (σ := Fin d) (R := 𝓡)

/-- 変数 `Y_i`。 -/
def var (i : Fin d) : DiagonalRing k d := MvPowerSeries.X (σ := Fin d) (R := 𝓡) i

/-- 対角線の元 `δ_i = C(X_i) − Y_i`。 -/
def diag (i : Fin d) : DiagonalRing k d := const k d (MvPowerSeries.X i) - var k d i

theorem algebraMap_X (i : Fin d) :
    algebraMap 𝓡 (DiagonalRing k d) (MvPowerSeries.X i) = var k d i :=
  MvPowerSeries.map_X _ i

theorem algebraMap_C (a : k) :
    algebraMap 𝓡 (DiagonalRing k d) (MvPowerSeries.C a) = const k d (MvPowerSeries.C a) :=
  MvPowerSeries.map_C _ _

instance : IsAdicComplete (maximalIdeal 𝓡) 𝓡 :=
  isAdicComplete_powerSeries_maximalIdeal (Fin d) k

theorem X_mem_maximalIdeal (i : Fin d) : (MvPowerSeries.X i : 𝓡) ∈ maximalIdeal 𝓡 := by
  rw [← mvPowerSeries_span_X_eq_maximalIdeal]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- 評価 `Δ : S → R`、`Y_i ↦ X_i`。 -/
noncomputable def eval : DiagonalRing k d →+* 𝓡 :=
  adicPowerSeriesEval (RingHom.id 𝓡) (maximalIdeal 𝓡) MvPowerSeries.X (X_mem_maximalIdeal k d)

@[simp] theorem eval_const (a : 𝓡) : eval k d (const k d a) = a :=
  adicPowerSeriesEval_C _ _ _ _ a

@[simp] theorem eval_var (i : Fin d) : eval k d (var k d i) = MvPowerSeries.X i :=
  adicPowerSeriesEval_X _ _ _ _ i

@[simp] theorem eval_diag (i : Fin d) : eval k d (diag k d i) = 0 := by
  simp [diag]

/-- `Δ ∘ i₂ = id`：定数と変数の上で一致するので、冪級数環からの環準同型の一意性による。 -/
theorem eval_algebraMap (a : 𝓡) : eval k d (algebraMap 𝓡 (DiagonalRing k d) a) = a := by
  have h : (eval k d).comp (algebraMap 𝓡 (DiagonalRing k d)) = RingHom.id 𝓡 := by
    apply MvPowerSeries.ringHom_ext_of_isHausdorff (maximalIdeal 𝓡)
    · ext a
      simp [algebraMap_C]
    · intro i
      simp [algebraMap_X]
    · intro i
      simpa [algebraMap_X] using X_mem_maximalIdeal k d i
  exact RingHom.congr_fun h a

theorem eval_surjective : Function.Surjective (eval k d) :=
  fun a ↦ ⟨const k d a, eval_const k d a⟩

/-- 対角線のイデアル `(δ)`。 -/
def diagIdeal : Ideal (DiagonalRing k d) := Ideal.span (Set.range (diag k d))

theorem diagIdeal_le_ker : diagIdeal k d ≤ RingHom.ker (eval k d) := by
  rw [diagIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact eval_diag k d i

/-- 多項式 `p` については `p ≡ C(Δ p) mod (δ)`。多項式環からの環準同型の一意性による。 -/
theorem coe_sub_const_eval_mem (p : MvPolynomial (Fin d) 𝓡) :
    ofPoly k d p - const k d (eval k d (ofPoly k d p)) ∈ diagIdeal k d := by
  rw [← Ideal.Quotient.eq]
  let φ : MvPolynomial (Fin d) 𝓡 →+* DiagonalRing k d ⧸ diagIdeal k d :=
    (Ideal.Quotient.mk _).comp (ofPoly k d)
  let ψ : MvPolynomial (Fin d) 𝓡 →+* DiagonalRing k d ⧸ diagIdeal k d :=
    ((Ideal.Quotient.mk _).comp ((const k d).comp (eval k d))).comp (ofPoly k d)
  have hC : ∀ a, ofPoly k d (MvPolynomial.C a) = const k d a := fun a ↦ MvPolynomial.coe_C a
  have hX : ∀ i, ofPoly k d (MvPolynomial.X i) = var k d i := fun i ↦ MvPolynomial.coe_X i
  have h : φ = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ, ψ, hC]
    · intro i
      simp only [φ, ψ, RingHom.coe_comp, Function.comp_apply, hX, eval_var]
      rw [Ideal.Quotient.eq]
      have : var k d i - const k d (MvPowerSeries.X i) = -diag k d i := by
        simp [diag]
      rw [this]
      exact (diagIdeal k d).neg_mem (Ideal.subset_span ⟨i, rfl⟩)
  exact RingHom.congr_fun h p

/-- 変数のイデアルの冪の評価は極大イデアルの冪に入る。 -/
theorem eval_mem_maximalIdeal_pow (N : ℕ) (r : DiagonalRing k d)
    (hr : r ∈ Ideal.span (Set.range (var k d)) ^ N) : eval k d r ∈ maximalIdeal 𝓡 ^ N := by
  have hle : (Ideal.span (Set.range (var k d)) ^ N).map (eval k d) ≤ maximalIdeal 𝓡 ^ N := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [eval_var]
    exact X_mem_maximalIdeal k d i
  exact hle (Ideal.mem_map_of_mem _ hr)

theorem var_mem_maximalIdeal (i : Fin d) : var k d i ∈ maximalIdeal (DiagonalRing k d) := by
  change MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin d) 𝓡)
  rw [powerSeries_maximalIdeal_eq]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

theorem const_mem_maximalIdeal {a : 𝓡} (ha : a ∈ maximalIdeal 𝓡) :
    const k d a ∈ maximalIdeal (DiagonalRing k d) := by
  change MvPowerSeries.C a ∈ maximalIdeal (MvPowerSeries (Fin d) 𝓡)
  rw [powerSeries_maximalIdeal_eq]
  exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

/-- **対角線のイデアルは評価の核**：`ker Δ = (δ)`。多項式での合同と切り捨ての評価から、
`f − C(Δ f)` は全ての `N` で `(δ) + m_S^N` に入り、Krull の交叉定理から `(δ)` に入る。 -/
theorem ker_eval : RingHom.ker (eval k d) = diagIdeal k d := by
  refine le_antisymm ?_ (diagIdeal_le_ker k d)
  intro f hf
  have hf0 : eval k d f = 0 := hf
  -- `f − C(Δ f)` は全ての `N` で `(δ) + m_S^N` に入る
  have hmem : ∀ N : ℕ, f - const k d (eval k d f) ∈
      diagIdeal k d ⊔ maximalIdeal (DiagonalRing k d) ^ N := by
    intro N
    let p : MvPolynomial (Fin d) 𝓡 := MvPowerSeries.truncTotal N (toPS k d f)
    let r : DiagonalRing k d := f - ofPoly k d p
    have hr : r ∈ Ideal.span (Set.range (var k d)) ^ N := by
      apply mem_span_X_pow_of_coeff N (toPS k d r)
      intro α hα
      change MvPowerSeries.coeff α (toPS k d f - (p : MvPowerSeries (Fin d) 𝓡)) = 0
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hα, sub_self]
    have hvar : Ideal.span (Set.range (var k d)) ≤ maximalIdeal (DiagonalRing k d) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact var_mem_maximalIdeal k d i
    have hrm : r ∈ maximalIdeal (DiagonalRing k d) ^ N := Ideal.pow_right_mono hvar N hr
    have hcm : const k d (eval k d r) ∈ maximalIdeal (DiagonalRing k d) ^ N := by
      have he := eval_mem_maximalIdeal_pow k d N r hr
      have hle : (maximalIdeal 𝓡 ^ N).map (const k d) ≤ maximalIdeal (DiagonalRing k d) ^ N := by
        rw [Ideal.map_pow]
        apply Ideal.pow_right_mono
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        exact const_mem_maximalIdeal k d ha
      exact hle (Ideal.mem_map_of_mem _ he)
    have hsplit : f - const k d (eval k d f) =
        (ofPoly k d p - const k d (eval k d (ofPoly k d p))) +
        (r - const k d (eval k d r)) := by
      simp only [r, map_sub]
      ring
    rw [hsplit]
    exact add_mem (Ideal.mem_sup_left (coe_sub_const_eval_mem k d p))
      (Ideal.mem_sup_right (sub_mem hrm hcm))
  -- Krull の交叉定理
  rw [hf0, map_zero, sub_zero] at hmem
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (R := DiagonalRing k d)
    (M := DiagonalRing k d ⧸ diagIdeal k d) (maximalIdeal (DiagonalRing k d))
    (maximalIdeal_le_jacobson _)
  have hx : (Ideal.Quotient.mk (diagIdeal k d) f) ∈
      (⨅ i : ℕ, maximalIdeal (DiagonalRing k d) ^ i • ⊤ :
        Submodule (DiagonalRing k d) (DiagonalRing k d ⧸ diagIdeal k d)) := by
    rw [Submodule.mem_iInf]
    intro N
    rw [Ideal.Quotient.mk_mem_smul_top_iff, sup_comm]
    exact hmem N
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx

/-- `S/(δ) ≅ R`（評価が誘導する環同型）。 -/
def quotDiagEquiv : (DiagonalRing k d ⧸ diagIdeal k d) ≃+* 𝓡 :=
  (Ideal.quotEquivOfEq (ker_eval k d).symm).trans
    (RingHom.quotientKerEquivOfSurjective (eval_surjective k d))

@[simp] theorem quotDiagEquiv_mk (f : DiagonalRing k d) :
    quotDiagEquiv k d (Ideal.Quotient.mk _ f) = eval k d f := rfl

instance : IsRegularLocalRing 𝓡 := isRegularLocalRing_mvPowerSeries_fin k d

instance : IsRegularLocalRing (DiagonalRing k d) :=
  isRegularLocalRing_mvPowerSeries_fin 𝓡 d

theorem ringKrullDim_eq : ringKrullDim (DiagonalRing k d) = ((d + d : ℕ) : WithBot ℕ∞) := by
  change ringKrullDim (MvPowerSeries (Fin d) 𝓡) = _
  rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_mvPowerSeries_field]
  push_cast
  rfl

/-- 対角線の元と定数の変数を並べた列。極大イデアルの極小生成系。 -/
def diagConst : Fin (d + d) → DiagonalRing k d :=
  Fin.append (diag k d) (fun i ↦ const k d (MvPowerSeries.X i))

theorem span_diagConst : Ideal.span (Set.range (diagConst k d)) = maximalIdeal (DiagonalRing k d) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
    · simp only [diagConst, Fin.append_left]
      exact sub_mem (const_mem_maximalIdeal k d (X_mem_maximalIdeal k d i))
        (var_mem_maximalIdeal k d i)
    · simp only [diagConst, Fin.append_right]
      exact const_mem_maximalIdeal k d (X_mem_maximalIdeal k d i)
  · have hm : maximalIdeal (DiagonalRing k d) =
        Ideal.span (const k d '' Set.range MvPowerSeries.X) ⊔ Ideal.span (Set.range (var k d)) := by
      have := powerSeries_maximalIdeal_eq (Fin d) 𝓡
      rw [← mvPowerSeries_span_X_eq_maximalIdeal, Ideal.map_span] at this
      exact this
    rw [hm, sup_le_iff, Ideal.span_le, Ideal.span_le]
    have hc : ∀ i, const k d (MvPowerSeries.X i) ∈ Ideal.span (Set.range (diagConst k d)) :=
      fun i ↦ Ideal.subset_span ⟨Fin.natAdd d i, Fin.append_right _ _ i⟩
    have hδ : ∀ i, diag k d i ∈ Ideal.span (Set.range (diagConst k d)) :=
      fun i ↦ Ideal.subset_span ⟨Fin.castAdd d i, Fin.append_left _ _ i⟩
    constructor
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hc i
    · rintro _ ⟨i, rfl⟩
      have : var k d i = const k d (MvPowerSeries.X i) - diag k d i := by simp [diag]
      change var k d i ∈ _
      rw [this]
      exact sub_mem (hc i) (hδ i)

/-- **対角線の元は正則列**：`δ_1, …, δ_d` は `S` の弱正則列。 -/
theorem isWeaklyRegular_diag :
    RingTheory.Sequence.IsWeaklyRegular (DiagonalRing k d) (List.ofFn (diag k d)) := by
  have h := isWeaklyRegular_of_span_eq_maximalIdeal (DiagonalRing k d) (diagConst k d)
    (span_diagConst k d) (ringKrullDim_eq k d)
  rw [diagConst, List.ofFn_fin_append, RingTheory.Sequence.isWeaklyRegular_append_iff] at h
  exact h.1

/-- 変数の取り替え `i₂` は局所準同型。 -/
instance : IsLocalHom (algebraMap 𝓡 (DiagonalRing k d)) := by
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal 𝓡 := (mem_maximalIdeal _).mpr hna
  rw [← mvPowerSeries_span_X_eq_maximalIdeal] at hm
  have hle : (Ideal.span (Set.range (MvPowerSeries.X : Fin d → 𝓡))).map
      (algebraMap 𝓡 (DiagonalRing k d)) ≤ maximalIdeal (DiagonalRing k d) := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [algebraMap_X]
    exact var_mem_maximalIdeal k d i
  exact (mem_maximalIdeal _).mp (hle (Ideal.mem_map_of_mem _ hm)) ha

end DiagonalRing

end SerrePositivity
