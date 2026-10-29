module

public import SerrePositivity.CommutativeAlgebra.CoefficientEvalDerivation
public import SerrePositivity.CommutativeAlgebra.ModuleDerivationDescent
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-! # 一元で生成される拡大への導分の延長

概要：体 `K` 上で一元 `x` が生成する可換環 `L`（`Algebra.adjoin K {x} = ⊤`）について、
導分 `δ : K → V` を `x ↦ v` となるよう `L` 上へ延長する。延長できるための必要十分条件は、
`x` の最小多項式 `f` について `f^δ(x) + f'(x) • v = 0`（`f^δ` は係数に `δ` を作用させた多項式）。
方針：多項式環上の導分 `f ↦ f^δ(x) + f'(x) • v` を、評価写像 `K[X] → L` の核 `(f)` に沿って降ろす。
必要性は Mathlib の `Derivation.apply_aeval_eq'`（評価の公式）から従う。`x` が整である仮定は不要。
規約：`V` は `L` 加群で、`R → K → L` の作用は整合しているとする。
使われ方：p 乗根の添加の導分（`PAdjoinDerivation`）と、Kähler 微分の非零性の判定。
Mathlib には微分体の分離的な場合（FieldTheory/Differential/Basic.lean）だけがあり、この一般形はない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial

variable {R K L V : Type*} [CommRing R] [Field K] [CommRing L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]

/-- 延長の両立条件の左辺 `f^δ(x) + f'(x) • v`（`f` は `x` の最小多項式）。 -/
def adjoinSingletonObstruction (x : L) (δ : Derivation R K V) (v : V) : V :=
  coefficientEvalLinearMap x δ (minpoly K x) + aeval x (derivative (minpoly K x)) • v

/-- 延長の構成と、その二つの性質（底体上で `δ` と一致、`x ↦ v`）。 -/
def adjoinSingletonDerivationAux (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (δ : Derivation R K V) (v : V) (h : adjoinSingletonObstruction x δ v = 0) :
    {Δ : Derivation R L V // (∀ c : K, Δ (algebraMap K L c) = δ c) ∧ Δ x = v} := by
  let : Algebra K[X] L := (aeval x).toRingHom.toAlgebra
  let : Module K[X] V := Module.compHom V (aeval x).toRingHom
  let : IsScalarTower K[X] L V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower R K[X] L := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L r = aeval x (C (algebraMap R K r))
    rw [aeval_C, IsScalarTower.algebraMap_apply R K L]
  let d₀ : Derivation R K[X] V :=
    { toLinearMap := coefficientEvalLinearMap x δ
      map_one_eq_zero' := by simpa only [← C_1, coefficientEvalLinearMap_C] using δ.map_one_eq_zero
      leibniz' := fun f g ↦ coefficientEvalLinearMap_leibniz x δ f g }
  let : IsScalarTower K K[X] V := ⟨fun c f w ↦ by
    change aeval x (c • f) • w = c • (aeval x f • w)
    rw [map_smul, smul_assoc]⟩
  let d : Derivation R K[X] V := d₀ + (Polynomial.mkDerivation K v).restrictScalars R
  have hd (f : K[X]) : d f = coefficientEvalLinearMap x δ f + aeval x (derivative f) • v := by
    simp only [d, d₀, Derivation.add_apply]
    rfl
  have hf : Function.Surjective (algebraMap K[X] L) := by
    intro y
    have hy : y ∈ (aeval (R := K) x).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval K x, hs]; trivial
    obtain ⟨f, hf⟩ := hy
    exact ⟨f, hf⟩
  have hker : ∀ f, algebraMap K[X] L f = 0 → d f = 0 := by
    intro f hf
    obtain ⟨g, rfl⟩ := minpoly.dvd_iff.mpr hf
    rw [d.leibniz, hd (minpoly K x), ← adjoinSingletonObstruction, h, smul_zero, add_zero]
    change aeval x (minpoly K x) • d g = 0
    rw [minpoly.aeval, zero_smul]
  refine ⟨descendModuleDerivation hf d hker, fun c ↦ ?_, ?_⟩
  · rw [← show algebraMap K[X] L (C c) = algebraMap K L c from aeval_C x c,
      descendModuleDerivation_apply, hd]
    simp
  · rw [← show algebraMap K[X] L X = x from aeval_X x, descendModuleDerivation_apply, hd]
    simp

/-- `δ` の延長で `x` を `v` に送るもの（両立条件の下で）。 -/
def adjoinSingletonDerivation (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (δ : Derivation R K V) (v : V) (h : adjoinSingletonObstruction x δ v = 0) :
    Derivation R L V :=
  (adjoinSingletonDerivationAux x hs δ v h).1

@[simp] theorem adjoinSingletonDerivation_algebraMap (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (δ : Derivation R K V) (v : V) (h : adjoinSingletonObstruction x δ v = 0) (c : K) :
    adjoinSingletonDerivation x hs δ v h (algebraMap K L c) = δ c :=
  (adjoinSingletonDerivationAux x hs δ v h).2.1 c

@[simp] theorem adjoinSingletonDerivation_self (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (δ : Derivation R K V) (v : V) (h : adjoinSingletonObstruction x δ v = 0) :
    adjoinSingletonDerivation x hs δ v h x = v :=
  (adjoinSingletonDerivationAux x hs δ v h).2.2

omit [IsScalarTower R K L] [IsScalarTower K L V] in
/-- 必要性：`δ` の延長 `Δ` があれば、`v = Δ x` で両立条件が成り立つ。 -/
theorem adjoinSingletonObstruction_eq_zero (x : L) (δ : Derivation R K V)
    (Δ : Derivation R L V) (hΔ : ∀ c : K, Δ (algebraMap K L c) = δ c) :
    adjoinSingletonObstruction x δ (Δ x) = 0 := by
  have := Derivation.apply_aeval_eq' δ Δ LinearMap.id (fun c ↦ (hΔ c).symm) x (minpoly K x)
  rw [minpoly.aeval, Δ.map_zero] at this
  exact this.symm

/-- `δ` を `x ↦ v` となるよう延長できることと、両立条件は同値。 -/
theorem exists_derivation_extension_iff (x : L) (hs : Algebra.adjoin K {x} = ⊤)
    (δ : Derivation R K V) (v : V) :
    (∃ Δ : Derivation R L V, (∀ c : K, Δ (algebraMap K L c) = δ c) ∧ Δ x = v) ↔
      adjoinSingletonObstruction x δ v = 0 :=
  ⟨fun ⟨Δ, hΔ, hx⟩ ↦ hx ▸ adjoinSingletonObstruction_eq_zero x δ Δ hΔ,
    fun h ↦ ⟨_, (adjoinSingletonDerivationAux x hs δ v h).2⟩⟩

/-- 生成元の最小多項式の微分が零（生成元が分離的でない）なら、生成元の Kähler 微分は零でない。
`δ = 0`、`v = 1` の延長で検出する。 -/
theorem kaehlerDifferential_D_ne_zero_of_derivative_minpoly_eq_zero {F E : Type*} [Field F]
    [CommRing E] [Nontrivial E] [Algebra F E] (x : E) (hs : Algebra.adjoin F {x} = ⊤)
    (h : derivative (minpoly F x) = 0) : KaehlerDifferential.D F E x ≠ 0 := by
  have h0 : (0 : Derivation F F E).mapCoeffs (minpoly F x) = 0 := by
    ext n
    simp
  have hob : adjoinSingletonObstruction x (0 : Derivation F F E) 1 = 0 := by
    simp [adjoinSingletonObstruction, h, coefficientEvalLinearMap, h0]
  intro hzero
  have heq := congrArg (adjoinSingletonDerivation x hs 0 1 hob).liftKaehlerDifferential hzero
  simp at heq

end SerrePositivity
