module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyBase
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# 有限根付き変数環の小数指数基底

## 概要
有限変数の根付きモノイド環は、通常の多項式環上で小数指数を基底とする自由加群。
## 方針
既存の一変数の指数分解を各座標に適用し、有限台関数を並べ替える。
## 規約
BS 著者版 Proposition 7.10 の Xi−fi の正則性の入力。係数環の非零性を仮定しない。
## 使われ方
有限正則列の基底変更と、商の p 冪ねじれの一様評価。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type v) [Finite J]
local notation "G" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "F" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootFraction p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "B" => rootFamilyRaw p R J

/-- 通常の自然数指数を根付き指数へ移す加法射。 -/
def rootFamilyNatExponent : (J →₀ ℕ) →+ (J →₀ G) :=
  Finsupp.mapRange.addMonoidHom
    { toFun := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent p (Nat.Prime.pos (Fact.out : p.Prime))
      map_zero' := by apply Subtype.ext; rfl
      map_add' := by intro a b; apply Subtype.ext; exact Nat.cast_add a b }

/-- 各変数の第零段の根を指定する通常多項式環の標準係数射。 -/
def rootFamilyPolynomialMap : MvPolynomial J R →+* B :=
  AddMonoidAlgebra.mapDomainRingHom R (rootFamilyNatExponent p J)

/-- 有限指数族を小数部分と自然数部分に分ける同値。 -/
def rootFamilyExponentSplit : (J →₀ G) ≃ ((J → F) × (J →₀ ℕ)) where
  toFun q := (fun j => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime)) (q j)).2,
    Finsupp.equivFunOnFinite.symm (fun j => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime)) (q j)).1))
  invFun q := Finsupp.equivFunOnFinite.symm
    (fun j => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))).symm (q.2 j, q.1 j))
  left_inv q := by
    apply Finsupp.ext
    intro j
    exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))).symm_apply_apply (q j)
  right_inv q := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.snd ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))).apply_symm_apply (q.2 j, q.1 j))
    · ext j
      exact congrArg Prod.fst ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))).apply_symm_apply (q.2 j, q.1 j))

/-- 整数指数の加算は小数部分を変えず、整数部分へ加わる。 -/
theorem rootFamilyExponentSplit_nat_add (d : J →₀ ℕ) (q : J →₀ G) :
    rootFamilyExponentSplit p J (rootFamilyNatExponent p J d + q) =
      ((rootFamilyExponentSplit p J q).1, d + (rootFamilyExponentSplit p J q).2) := by
  apply Prod.ext
  · funext j
    change (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent p (Nat.Prime.pos (Fact.out : p.Prime)) (d j) + q j)).2 = _
    have h := congrArg (fun z : ℕ × F => z.2)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit_nat_add p (Nat.Prime.pos (Fact.out : p.Prime)) (d j) (q j))
    exact h
  · apply Finsupp.ext
    intro j
    change (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit p (Nat.Prime.pos (Fact.out : p.Prime))
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent p (Nat.Prime.pos (Fact.out : p.Prime)) (d j) + q j)).1 = _
    exact congrArg (fun z : ℕ × F => z.1) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentSplit_nat_add p (Nat.Prime.pos (Fact.out : p.Prime)) (d j) (q j))

/-- 小数部分ごとに通常多項式を並べる係数環上の線形同型。 -/
def rootFamilyFractionCoordinates : B ≃ₗ[R] ((J → F) →₀ MvPolynomial J R) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.domLCongr (rootFamilyExponentSplit p J)).trans
      ((Finsupp.curryLinearEquiv R).trans
        (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv R).symm)))

/-- 単項式の座標は、小数指数成分に置いた整数指数の通常単項式。 -/
theorem rootFamilyFractionCoordinates_single (q : J →₀ G) (a : R) :
    rootFamilyFractionCoordinates p R J (AddMonoidAlgebra.single q a) =
      Finsupp.single (rootFamilyExponentSplit p J q).1
        (MvPolynomial.monomial (rootFamilyExponentSplit p J q).2 a) := by
  simp [rootFamilyFractionCoordinates, Finsupp.curry_single]
  rfl

/-- 多項式の単項式は整数指数の単項式として根付き変数環へ入る。 -/
theorem rootFamilyPolynomialMap_monomial (d : J →₀ ℕ) (a : R) :
    rootFamilyPolynomialMap p R J (MvPolynomial.monomial d a) =
      AddMonoidAlgebra.single (rootFamilyNatExponent p J d) a :=
  by exact AddMonoidAlgebra.mapDomain_single

/-- 小数指数座標は通常多項式環の作用と両立する。 -/
theorem rootFamilyFractionCoordinates_smul :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    ∀ (f : MvPolynomial J R) (x : B),
      rootFamilyFractionCoordinates p R J (f • x) = f • rootFamilyFractionCoordinates p R J x := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  intro f x
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [add_smul, map_add, hf, hg, add_smul]
  | monomial d a =>
      let e0 : B ≃ₗ[R] ((J →₀ G) →₀ R) := AddMonoidAlgebra.coeffLinearEquiv R
      obtain ⟨v, rfl⟩ := e0.symm.surjective x
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw =>
          change rootFamilyFractionCoordinates p R J
            ((MvPolynomial.monomial d a) • AddMonoidAlgebra.ofCoeff v) =
              (MvPolynomial.monomial d a) • rootFamilyFractionCoordinates p R J (AddMonoidAlgebra.ofCoeff v) at hv
          change rootFamilyFractionCoordinates p R J
            ((MvPolynomial.monomial d a) • AddMonoidAlgebra.ofCoeff w) =
              (MvPolynomial.monomial d a) • rootFamilyFractionCoordinates p R J (AddMonoidAlgebra.ofCoeff w) at hw
          change rootFamilyFractionCoordinates p R J
            ((MvPolynomial.monomial d a) •
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)) =
              (MvPolynomial.monomial d a) • rootFamilyFractionCoordinates p R J
                (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)
          rw [smul_add, map_add, hv, hw, map_add, smul_add]
      | single q b =>
          change rootFamilyFractionCoordinates p R J
            (rootFamilyPolynomialMap p R J (MvPolynomial.monomial d a) *
              AddMonoidAlgebra.single q b) =
              (MvPolynomial.monomial d a) • rootFamilyFractionCoordinates p R J
                (AddMonoidAlgebra.single q b)
          rw [rootFamilyPolynomialMap_monomial, AddMonoidAlgebra.single_mul_single,
            rootFamilyFractionCoordinates_single, rootFamilyFractionCoordinates_single,
            rootFamilyExponentSplit_nat_add]
          simp [Finsupp.smul_single, smul_eq_mul, MvPolynomial.monomial_mul_monomial]

/-- 概要：小数指数座標は通常多項式環上でも線形同型。
方針：係数環上の座標同型へ検証した作用の保存を加える。
規約：BS 著者版 Proposition 7.10 の完備化前。使われ方：正則列と商の評価。 -/
def rootFamilyFractionLinearEquiv :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    B ≃ₗ[MvPolynomial J R] ((J → F) →₀ MvPolynomial J R) := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  exact { (rootFamilyFractionCoordinates p R J).toAddEquiv with
    map_smul' := rootFamilyFractionCoordinates_smul p R J }

/-- 小数指数は通常多項式環上の実際の自由基底を与える。 -/
def rootFamilyFractionBasis :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    Module.Basis (J → F) (MvPolynomial J R) B := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  exact Module.Basis.ofRepr (rootFamilyFractionLinearEquiv p R J)

end SerrePositivity.BhattScholze.Semiperfectoid
