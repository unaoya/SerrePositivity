module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.Adic.Finite
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # 完備環への冪級数の評価と準同型の一意性

概要：`S` が `J` 進完備で `x_i ∈ J` のとき、係数写像 `f : R → S` と変数の像 `x` から評価
`R[[X]] → S` を作る（`adicPowerSeriesEval`）。変数の像が `J` を生成し係数が `S/J` へ全射なら評価は全射、
`S/J` が `R` 上有限なら評価は有限。逆に、`J` 進分離な環への二つの準同型は、定数と変数の上で一致すれば等しい。
方針：評価は、係数に離散位相、`S` に `J` 進位相を入れて Mathlib の `MvPowerSeries.eval₂Hom` を使う。
一意性は、全次数 `N` での切り捨てとの差が `(X)^N` に入ること（`mem_powerSeries_variables_pow_iff`）による。
規約：Noether 性・局所性・係数写像の単射性は仮定しない。
使われ方：Cohen–Gabber と Witt の正規化、完備化の Noether 性、交点数の対角線論法。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Eval

variable {R S : Type*} [CommRing R] [CommRing S]
variable (f : R →+* S) (J : Ideal S) [IsAdicComplete J S]
variable {σ : Type*} [Finite σ] (x : σ → S) (hx : ∀ i, x i ∈ J)

/-- 指定イデアル内の有限列への冪級数評価。完備性をMathlibの位相的条件へ移して構成する。 -/
noncomputable def adicPowerSeriesEval : MvPowerSeries σ R →+* S := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  let : CompleteSpace S := (IsAdic.isPrecomplete_iff (show IsAdic J from rfl)).mp inferInstance
  let : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp inferInstance
  have he : MvPowerSeries.HasEval x := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
    · simp
  exact MvPowerSeries.eval₂Hom (φ := f) continuous_of_discreteTopology he

/-- 評価は係数上で元の環写像と一致する。 -/
@[simp] theorem adicPowerSeriesEval_C (r : R) :
    adicPowerSeriesEval f J x hx (MvPowerSeries.C r) = f r := by
  simp [adicPowerSeriesEval, MvPowerSeries.coe_eval₂Hom]

/-- 評価は各形式変数を指定した元へ送る。 -/
@[simp] theorem adicPowerSeriesEval_X (i : σ) :
    adicPowerSeriesEval f J x hx (MvPowerSeries.X i) = x i := by
  simp [adicPowerSeriesEval, MvPowerSeries.coe_eval₂Hom]

/-- 形式変数のイデアルの像は、指定した元のイデアルである。 -/
theorem adicPowerSeriesEval_map_span :
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))).map
      (adicPowerSeriesEval f J x hx) = Ideal.span (Set.range x) := by
  rw [Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, adicPowerSeriesEval_X]

/-- 変数の像が完備イデアルを生成し、係数がその商へ全射なら、冪級数評価は全射。
商での全射を反映するMathlibの一般定理を用い、局所性・Noether性は使わない。 -/
theorem adicPowerSeriesEval_surjective
    (hspan : Ideal.span (Set.range x) = J)
    (hf : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Surjective (adicPowerSeriesEval f J x hx) := by
  let g := adicPowerSeriesEval f J x hx
  let I : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : I.map g = J := (adicPowerSeriesEval_map_span f J x hx).trans hspan
  have : IsHausdorff (I.map g) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := I) g
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := hf (Ideal.Quotient.mk J y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (I.map g) (g (MvPowerSeries.C r)) = _
  rw [adicPowerSeriesEval_C, Ideal.Quotient.eq, hmap]
  exact Ideal.Quotient.eq.mp hr

/-- 有限な閉ファイバーと始域の前完備性から、冪級数評価の有限性を得る。
イデアルHを明示するので、等標数の(X)と混標数の(p,X)の双方に使える。
Hの前完備性は実現側で確認する独立した条件である。 -/
theorem adicPowerSeriesEval_finite [Algebra R S]
    (H : Ideal (MvPowerSeries σ R)) [IsPrecomplete H (MvPowerSeries σ R)]
    (hmap : H.map (adicPowerSeriesEval (algebraMap R S) J x hx) = J)
    [Module.Finite R (S ⧸ J)] :
    (adicPowerSeriesEval (algebraMap R S) J x hx).Finite := by
  let g := adicPowerSeriesEval (algebraMap R S) J x hx
  let : Algebra (MvPowerSeries σ R) S := g.toAlgebra
  let : IsScalarTower R (MvPowerSeries σ R) S :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (adicPowerSeriesEval_C _ J x hx r).symm)
  let : Module.Finite (MvPowerSeries σ R) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact finite_algebra_of_finite_quotient_map H S J hmap

/-- 変数イデアルの像で割った商が係数環上有限なら、等標数形の評価は有限。
変数イデアルについての冪級数環の完備性をMathlibから供給する。 -/
theorem adicPowerSeriesEval_finite_of_span [Algebra R S]
    (hspan : Ideal.span (Set.range x) = J) [Module.Finite R (S ⧸ J)] :
    (adicPowerSeriesEval (algebraMap R S) J x hx).Finite := by
  apply adicPowerSeriesEval_finite J x hx
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)))
  exact (adicPowerSeriesEval_map_span _ J x hx).trans hspan

end Eval

section RingHomExt

universe u

open MvPowerSeries


variable {K : Type u} [CommRing K] {σ : Type*}

/-- 全次数 `N` 未満の係数が消える冪級数は `(X)^N` に入る。 -/
theorem mem_span_X_pow_of_coeff [Finite σ] (N : ℕ) (f : MvPowerSeries σ K)
    (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N :=
  (mem_powerSeries_variables_pow_iff N f).mpr hf

/-- **冪級数環からの環準同型の一意性**：定数と変数の上で一致し、変数の像が `J` に入り、
`B` が `J` 進分離的なら、二つの環準同型は等しい。全次数の切り捨てとの差が `(X)^N` に入ることによる。 -/
theorem MvPowerSeries.ringHom_ext_of_isHausdorff [Finite σ] {B : Type*} [CommRing B]
    (J : Ideal B) [IsHausdorff J B] {φ ψ : MvPowerSeries σ K →+* B}
    (hC : φ.comp C = ψ.comp C) (hX : ∀ i, φ (X i) = ψ (X i)) (hJ : ∀ i, φ (X i) ∈ J) :
    φ = ψ := by
  classical
  let := Fintype.ofFinite σ
  -- 多項式の上では一致する
  have hpoly : φ.comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := K)) =
      ψ.comp MvPolynomial.coeToMvPowerSeries.ringHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := RingHom.congr_fun hC a
      simpa using this
    · intro i
      simpa using hX i
  -- 変数のイデアルの冪の像は `J` の冪に入る
  have hmap : ∀ N, ∀ r ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N,
      φ r ∈ J ^ N ∧ ψ r ∈ J ^ N := by
    intro N r hr
    have hle : ∀ χ : MvPowerSeries σ K →+* B, (∀ i, χ (X i) ∈ J) →
        (Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N).map χ ≤ J ^ N := by
      intro χ hχ
      rw [Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hχ i
    exact ⟨hle φ hJ (Ideal.mem_map_of_mem _ hr),
      hle ψ (fun i ↦ hX i ▸ hJ i) (Ideal.mem_map_of_mem _ hr)⟩
  ext f
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (inferInstance : IsHausdorff J B)
  intro N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  set p : MvPolynomial σ K := MvPowerSeries.truncTotal N f
  have hr : f - (p : MvPowerSeries σ K) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N := by
    apply mem_span_X_pow_of_coeff
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hα, sub_self]
  have hp : φ (p : MvPowerSeries σ K) = ψ p := RingHom.congr_fun hpoly p
  have hsplit : φ f - ψ f = φ (f - p) - ψ (f - p) := by
    rw [map_sub, map_sub, hp]
    ring
  rw [hsplit]
  exact sub_mem (hmap N _ hr).1 (hmap N _ hr).2

end RingHomExt

end SerrePositivity
