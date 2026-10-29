module

public import SerrePositivity.FieldTheory.AdjoinSingletonDerivation
public import SerrePositivity.RingTheory.Kaehler
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 一元で生成される非分離な拡大の Kähler 微分

概要：体 `K` 上で一元 `x` が体 `L` を生成し、`x` の最小多項式 `f` の微分が零（`x` が分離的でない）とする。
Kähler 微分の第一基本完全列 `L ⊗_K Ω_{K/R} → Ω_{L/R} → Ω_{L/K} → 0` について次を示す。
- `Ω_{L/K}` は `D x` を基底とする1次元。
- 左の写像 `mapBaseChange` の核は、関係式の微分 `f^D(x) = Σ xⁱ ⊗ D(fᵢ)` の張る直線。
- その元が零でなければ `dim Ω_{L/R} = dim Ω_{K/R}`。
方針：核の逆の包含は、核の候補で割った加群へ `D` を延長する（`adjoinSingletonDerivation`、`v = 0`）ことで、
普遍性から得る。順の包含は延長の必要条件（`adjoinSingletonObstruction_eq_zero`）から得る。
規約：`f^D(x)` は `relationDifferential`。係数作用の評価が `L` 線形写像と可換であることを補題にする。
使われ方：p 乗根の添加（`PrimeRootDifferentialRank`）での次元の安定。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial
open scoped TensorProduct

section Naturality

variable {R K L V W : Type*} [CommRing R] [CommRing K] [CommRing L]
  [Algebra R K] [Algebra R L] [Algebra K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]
  [AddCommGroup W] [Module R W] [Module K W] [Module L W]
  [IsScalarTower R K W] [IsScalarTower R L W] [IsScalarTower K L W]

/-- 係数作用の評価は `L` 線形写像と可換。 -/
theorem coefficientEvalLinearMap_compDer (x : L) (δ : Derivation R K V) (φ : V →ₗ[L] W)
    (f : K[X]) :
    coefficientEvalLinearMap x ((φ.restrictScalars K).compDer δ) f =
      φ (coefficientEvalLinearMap x δ f) := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, coefficientEvalLinearMap_leibniz x _ (C a * X ^ n) X,
      coefficientEvalLinearMap_leibniz x δ (C a * X ^ n) X, ih, coefficientEvalLinearMap_X,
      coefficientEvalLinearMap_X, smul_zero, smul_zero, zero_add, zero_add, map_smul]

end Naturality

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]

variable (R) in
/-- 関係式の微分 `f^D(x) = Σ xⁱ ⊗ D(fᵢ) ∈ L ⊗_K Ω_{K/R}`（`f` は `x` の最小多項式）。 -/
def relationDifferential (x : L) : L ⊗[K] KaehlerDifferential R K :=
  coefficientEvalLinearMap x
    ((TensorProduct.mk K L (KaehlerDifferential R K) 1).compDer (KaehlerDifferential.D R K))
    (minpoly K x)

/-- 生成元の最小多項式の微分が零なら、`D x` は `Ω_{L/K}` の基底。 -/
def kaehlerDifferentialBasisOfAdjoinSingleton (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (h : derivative (minpoly K x) = 0) : Module.Basis Unit L (KaehlerDifferential K L) :=
  Module.Basis.mk (v := fun _ : Unit ↦ KaehlerDifferential.D K L x)
    (linearIndependent_unique_iff.mpr
      (kaehlerDifferential_D_ne_zero_of_derivative_minpoly_eq_zero x hs h))
    (by simpa only [Set.range_const, Set.image_singleton] using
      (span_kaehlerDifferential_of_adjoin_eq_top {x} hs).ge)

@[simp] theorem kaehlerDifferentialBasisOfAdjoinSingleton_apply (x : L)
    (hs : Algebra.adjoin K {x} = ⊤) (h : derivative (minpoly K x) = 0) (i : Unit) :
    kaehlerDifferentialBasisOfAdjoinSingleton x hs h i = KaehlerDifferential.D K L x :=
  Module.Basis.mk_apply _ _ _

theorem finrank_kaehlerDifferential_of_adjoin_singleton (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (h : derivative (minpoly K x) = 0) : Module.finrank L (KaehlerDifferential K L) = 1 := by
  simpa using Module.finrank_eq_card_basis (kaehlerDifferentialBasisOfAdjoinSingleton x hs h)

/-- 関係式の微分は `mapBaseChange` で零に写る。 -/
theorem mapBaseChange_relationDifferential (x : L) (h : derivative (minpoly K x) = 0) :
    KaehlerDifferential.mapBaseChange R K L (relationDifferential R x) = 0 := by
  have := adjoinSingletonObstruction_eq_zero x
    (((KaehlerDifferential.mapBaseChange R K L).restrictScalars K).compDer
      ((TensorProduct.mk K L (KaehlerDifferential R K) 1).compDer (KaehlerDifferential.D R K)))
    (KaehlerDifferential.D R L) (fun c ↦ by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D])
  rw [adjoinSingletonObstruction, h, map_zero, zero_smul, add_zero,
    coefficientEvalLinearMap_compDer] at this
  exact this

/-- 核の決定：`ker (L ⊗_K Ω_{K/R} → Ω_{L/R})` は関係式の微分の張る直線。 -/
theorem ker_mapBaseChange_of_adjoin_singleton (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (h : derivative (minpoly K x) = 0) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange R K L) = L ∙ relationDifferential R x := by
  let M := L ⊗[K] KaehlerDifferential R K
  let N : Submodule L M := L ∙ relationDifferential R x
  let Q := M ⧸ N
  let : Module K Q := Module.compHom Q (algebraMap K L)
  let : Module R Q := Module.compHom Q (algebraMap R L)
  let : MulAction K Q := (Module.compHom Q (algebraMap K L)).toMulAction
  let : MulAction R Q := (Module.compHom Q (algebraMap R L)).toMulAction
  let : SMul K Q := (Module.compHom Q (algebraMap K L)).toSMul
  let : SMul R Q := (Module.compHom Q (algebraMap R L)).toSMul
  let : IsScalarTower K L Q :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := L) (M := Q) fun _ _ ↦ rfl
  let : IsScalarTower R L Q :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := L) (M := Q) fun _ _ ↦ rfl
  let : IsScalarTower R K Q :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := K) (M := Q) fun r q ↦ by
      change algebraMap K L (algebraMap R K r) • q = algebraMap R L r • q
      rw [IsScalarTower.algebraMap_apply R K L]
  let i : KaehlerDifferential R K →ₗ[K] M := TensorProduct.mk K L (KaehlerDifferential R K) 1
  let δ₀ : Derivation R K M := i.compDer (KaehlerDifferential.D R K)
  let δ : Derivation R K Q := (N.mkQ.restrictScalars K).compDer δ₀
  have hob : adjoinSingletonObstruction x δ 0 = 0 := by
    rw [adjoinSingletonObstruction, smul_zero, add_zero, coefficientEvalLinearMap_compDer]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.mem_span_singleton_self _)
  let Δ := adjoinSingletonDerivation x hs δ 0 hob
  let F := Δ.liftKaehlerDifferential.comp (KaehlerDifferential.mapBaseChange R K L)
  have hi : (F.restrictScalars K).comp i = (N.mkQ.restrictScalars K).comp i := by
    apply Derivation.liftKaehlerDifferential_unique
    ext c
    change Δ.liftKaehlerDifferential
      (KaehlerDifferential.mapBaseChange R K L
        ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K c)) = δ c
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D, adjoinSingletonDerivation_algebraMap]
  have he : F = N.mkQ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro l ω
    have hiω := congrArg (fun f : KaehlerDifferential R K →ₗ[K] Q ↦ f ω) hi
    change F ((1 : L) ⊗ₜ[K] ω) = N.mkQ ((1 : L) ⊗ₜ[K] ω) at hiω
    have ht : l ⊗ₜ[K] ω = l • ((1 : L) ⊗ₜ[K] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, map_smul, hiω]
  apply le_antisymm
  · intro y hy
    have hz : N.mkQ y = 0 := by
      rw [← he]
      change Δ.liftKaehlerDifferential (KaehlerDifferential.mapBaseChange R K L y) = 0
      rw [show KaehlerDifferential.mapBaseChange R K L y = 0 from hy, map_zero]
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  · apply Submodule.span_le.mpr
    rintro y rfl
    exact mapBaseChange_relationDifferential x h

/-- 関係式の微分が零でなければ、`Ω` の次元は拡大で変わらない。 -/
theorem finrank_kaehlerDifferential_eq_of_adjoin_singleton (F : Type*) [Field F] [Algebra F K]
    [Algebra F L] [IsScalarTower F K L] [Module.Finite F K] [Module.Finite K L]
    (x : L) (hs : Algebra.adjoin K {x} = ⊤) (h : derivative (minpoly K x) = 0)
    (hc : relationDifferential (K := K) F x ≠ 0) :
    Module.finrank L (KaehlerDifferential F L) = Module.finrank K (KaehlerDifferential F K) := by
  let : Module.Finite F L := Module.Finite.trans (R := F) K L
  have hn := LinearMap.finrank_range_add_finrank_ker (KaehlerDifferential.mapBaseChange F K L)
  rw [Module.finrank_baseChange, ker_mapBaseChange_of_adjoin_singleton x hs h,
    finrank_span_singleton hc] at hn
  have hd := LinearMap.finrank_range_add_finrank_ker (KaehlerDifferential.map F K L L)
  rw [LinearMap.range_eq_top.mpr (KaehlerDifferential.map_surjective F K L), finrank_top,
    finrank_kaehlerDifferential_of_adjoin_singleton x hs h,
    ← KaehlerDifferential.range_mapBaseChange F K L] at hd
  omega

end SerrePositivity
