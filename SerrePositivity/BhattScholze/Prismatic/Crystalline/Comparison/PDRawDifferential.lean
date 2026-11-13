module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPDerivation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# 未完備 pd de Rham 列の偏微分

## 概要
第 0 頂点の多項式座標と分冪差座標の偏微分を定める。

## 方針
係数の二つのテンソル因子の一方に偏微分を作用させる。

## 規約
差座標の偏微分は分冪の指数を一つ下げる。

## 使われ方
pd de Rham 微分と列の Poincaré 収縮。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 第 0 頂点の座標と、他の頂点の第 0 頂点との差を添字付ける。 -/
abbrev pdCoordinates (r n : ℕ) := Fin r ⊕ (Fin r × Fin n)

section TensorDerivation

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

local notation "T" => A ⊗[k] B
local notation "J" => TrivSqZeroExt T T

private def relativeJet {A' : Type u} [CommRing A'] [Algebra k A'] (f : A' →ₐ[k] T)
    (d : Derivation k A' A') : A' →ₐ[k] J where
  toFun x := (f x, f (d x))
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by change f (d 0) = 0; simp)
  map_one' := TrivSqZeroExt.ext (map_one _) (by change f (d 1) = 0; simp)
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (by
    change f (d (x+y)) = f (d x) + f (d y)
    rw [map_add, map_add])
  map_mul' x y := TrivSqZeroExt.ext (map_mul _ _ _) (by
    change f (d (x*y)) = f x * f (d y) + MulOpposite.op (f y) • f (d x)
    rw [op_smul_eq_smul, d.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rfl)
  commutes' a := TrivSqZeroExt.ext (f.commutes a) (by
    change f (d (algebraMap k A' a)) = 0
    rw [d.map_algebraMap, map_zero])

private def tensorJet (d : Derivation k A A) (e : Derivation k B B) : T →ₐ[k] J :=
  Algebra.TensorProduct.lift
    (relativeJet Algebra.TensorProduct.includeLeft d)
    (relativeJet Algebra.TensorProduct.includeRight e) (fun _ _ => Commute.all _ _)

private theorem tensorJet_fst (d : Derivation k A A) (e : Derivation k B B) (x : T) :
    (tensorJet d e x).fst = x := by
  have h : (TrivSqZeroExt.fstHom k T T).comp (tensorJet d e) = AlgHom.id k T := by
    apply Algebra.TensorProduct.ext
    · ext a
      change (tensorJet d e ((a : A) ⊗ₜ[k] (1 : B))).fst = a ⊗ₜ[k] (1 : B)
      rw [tensorJet, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    · ext b
      change (tensorJet d e ((1 : A) ⊗ₜ[k] (b : B))).fst = (1 : A) ⊗ₜ[k] b
      rw [tensorJet, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  exact DFunLike.congr_fun h x

private def tensorDerivation (d : Derivation k A A) (e : Derivation k B B) : Derivation k T T :=
  Derivation.mk' ((TrivSqZeroExt.sndHom T T).restrictScalars k ∘ₗ (tensorJet d e).toLinearMap)
    (fun x y => by
      change (tensorJet d e (x * y)).snd = x • (tensorJet d e y).snd + y • (tensorJet d e x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, tensorJet_fst, tensorJet_fst, op_smul_eq_smul])

private theorem tensorDerivation_tmul (d : Derivation k A A) (e : Derivation k B B) (a : A) (b : B) :
    tensorDerivation d e (a ⊗ₜ[k] b) = (d a) ⊗ₜ[k] b + a ⊗ₜ[k] (e b) := by
  change (tensorJet d e (a ⊗ₜ[k] b)).snd = _
  rw [tensorJet, Algebra.TensorProduct.lift_tmul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  change (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] e b) +
    ((1 : A) ⊗ₜ[k] b) * (d a ⊗ₜ[k] (1 : B)) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul, add_comm]

end TensorDerivation

variable (k : Type u) [CommRing k] (r n : ℕ)

local notation "S" => (Fin r × Fin n)
local notation "B" => MvPolynomial (Fin r) k
local notation "D" => DividedPowerAlgebra k (S →₀ k)

/-- 未完備 pd 係数環上の座標ごとの偏微分。 -/
def pdRawPartial : pdCoordinates r n → (pdRaw k r n →ₗ[k] pdRaw k r n)
  | .inl a => TensorProduct.map (MvPolynomial.pderiv a).toLinearMap LinearMap.id
  | .inr a => TensorProduct.map LinearMap.id (freeDPPartial a).toLinearMap

@[simp] private theorem partial_inl_tmul (a : Fin r) (f : B) (g : D) :
    pdRawPartial k r n (.inl a) (f ⊗ₜ[k] g) = MvPolynomial.pderiv a f ⊗ₜ[k] g :=
  TensorProduct.map_tmul _ _ _ _

@[simp] private theorem partial_inr_tmul (a : S) (f : B) (g : D) :
    pdRawPartial k r n (.inr a) (f ⊗ₜ[k] g) = f ⊗ₜ[k] freeDPPartial a g :=
  TensorProduct.map_tmul _ _ _ _

/-- 各座標での pd 偏微分は互いに可換。 -/
theorem pdRawPartial_comm (a b : pdCoordinates r n) (x : pdRaw k r n) :
    pdRawPartial k r n a (pdRawPartial k r n b x) =
      pdRawPartial k r n b (pdRawPartial k r n a x) := by
  let A := pdRawPartial k r n a
  let B' := pdRawPartial k r n b
  suffices h : A.comp B' = B'.comp A from DFunLike.congr_fun h x
  apply TensorProduct.ext'
  intro f g
  change pdRawPartial k r n a (pdRawPartial k r n b (f ⊗ₜ[k] g)) =
    pdRawPartial k r n b (pdRawPartial k r n a (f ⊗ₜ[k] g))
  rcases a with a | a <;> rcases b with b | b
  · simp only [partial_inl_tmul]
    have h : ⁅MvPolynomial.pderiv (R := k) a, MvPolynomial.pderiv (R := k) b⁆ = 0 := by
      apply MvPolynomial.derivation_ext
      intro t
      simp only [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
      split <;> split <;> simp
    have e : MvPolynomial.pderiv a (MvPolynomial.pderiv b f) =
        MvPolynomial.pderiv b (MvPolynomial.pderiv a f) := by
      apply sub_eq_zero.mp
      simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
        congrArg (fun d : Derivation k B B => d f) h
    rw [e]
  · simp
  · simp
  · simp only [partial_inr_tmul]
    rw [freeDPPartial_comm]

/-- 差座標の分冪に偏微分を施したときの値。 -/
theorem pdRawPartial_dp_succ (a : S) (m : ℕ) (x : S →₀ k) :
    pdRawPartial k r n (.inr a) ((1 : B) ⊗ₜ[k] DividedPowerAlgebra.dp k (m + 1) x) =
      (x a) • ((1 : B) ⊗ₜ[k] DividedPowerAlgebra.dp k m x) := by
  rw [partial_inr_tmul, freeDPPartial_dp_succ, TensorProduct.tmul_smul]

/-- 偏微分を導分として読む。 -/
def pdRawDerivation : pdCoordinates r n → Derivation k (pdRaw k r n) (pdRaw k r n)
  | .inl a => tensorDerivation (MvPolynomial.pderiv a) 0
  | .inr a => tensorDerivation 0 (freeDPPartial a)

/-- 導分の台の線形写像は座標ごとの pd 偏微分。 -/
theorem pdRawDerivation_toLinearMap (a : pdCoordinates r n) :
    (pdRawDerivation k r n a).toLinearMap = pdRawPartial k r n a := by
  apply TensorProduct.ext'
  intro f g
  rcases a with a | a
  · change tensorDerivation (MvPolynomial.pderiv a) 0 (f ⊗ₜ[k] g) = _
    simp only [tensorDerivation_tmul, Derivation.zero_apply, TensorProduct.tmul_zero, add_zero,
      partial_inl_tmul]
  · change tensorDerivation 0 (freeDPPartial a) (f ⊗ₜ[k] g) = _
    simp only [tensorDerivation_tmul, Derivation.zero_apply, TensorProduct.zero_tmul, zero_add,
      partial_inr_tmul]

end SerrePositivity.BhattScholze.Prismatic
