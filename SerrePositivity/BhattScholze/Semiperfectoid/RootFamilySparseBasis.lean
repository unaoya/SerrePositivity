module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootFamilyFractionBasis

/-!
# 任意の根付き変数族の有限台小数指数基底

## 概要
一変数の指数分解を有限台関数へ移し、任意添字の通常多項式環上の自由基底を作る。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## RootFamilySparseFraction -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "F" => PowerRootFraction p hp

/-- 小数指数の零元。有限台関数の零値として用いる。 -/
instance rootFamilyFractionZero : Zero F := ⟨⟨0, by norm_num⟩⟩

/-- 一変数の指数分解は零指数を零の組へ送る。 -/
theorem rootFamilyScalarSplit_zero : powerRootExponentSplit p hp 0 = (0, (0 : F)) := by
  apply Prod.ext
  · change ⌊(0 : ℚ)⌋₊ = 0
    norm_num
  · apply Subtype.ext
    apply Subtype.ext
    change Int.fract (0 : ℚ) = 0
    norm_num

variable (J : Type v)

/-- 任意添字の指数の整数部分。零を保つため有限台を持つ。 -/
def rootFamilyIntegerPart (q : J →₀ G) : J →₀ ℕ :=
  Finsupp.mapRange (fun x => (powerRootExponentSplit p hp x).1)
    (congrArg Prod.fst (rootFamilyScalarSplit_zero p)) q

/-- 任意添字の指数の小数部分。零を保つため有限台を持つ。 -/
def rootFamilySparseFractionPart (q : J →₀ G) : J →₀ F :=
  Finsupp.mapRange (fun x => (powerRootExponentSplit p hp x).2)
    (congrArg Prod.snd (rootFamilyScalarSplit_zero p)) q

/-- 小数部分と整数部分を足して元の有限台指数を戻す。 -/
def rootFamilySparseJoin (q : (J →₀ F) × (J →₀ ℕ)) : J →₀ G :=
  Finsupp.zipWith (fun a n => (powerRootExponentSplit p hp).symm (n, a))
    (by rw [← rootFamilyScalarSplit_zero p]; exact (powerRootExponentSplit p hp).symm_apply_apply 0)
    q.1 q.2

/-- 概要：任意添字の有限台指数の小数・整数分解。
方針：各座標で一変数の分解の両逆を使う。
規約：BS 著者版 Proposition 7.10。無限の小数指数族は使わない。
使われ方：通常多項式環上の自由基底の添字。 -/
def rootFamilySparseExponentSplit : (J →₀ G) ≃ ((J →₀ F) × (J →₀ ℕ)) where
  toFun q := (rootFamilySparseFractionPart p J q, rootFamilyIntegerPart p J q)
  invFun := rootFamilySparseJoin p J
  left_inv q := by
    apply Finsupp.ext
    intro j
    exact (powerRootExponentSplit p hp).symm_apply_apply (q j)
  right_inv q := by
    apply Prod.ext
    · apply Finsupp.ext
      intro j
      exact congrArg Prod.snd ((powerRootExponentSplit p hp).apply_symm_apply (q.2 j, q.1 j))
    · apply Finsupp.ext
      intro j
      exact congrArg Prod.fst ((powerRootExponentSplit p hp).apply_symm_apply (q.2 j, q.1 j))

/-- 整数指数の加算は有限台の小数部分を変えない。 -/
theorem rootFamilySparseExponentSplit_nat_add (d : J →₀ ℕ) (q : J →₀ G) :
    rootFamilySparseExponentSplit p J (rootFamilyNatExponent p J d + q) =
      ((rootFamilySparseExponentSplit p J q).1, d + (rootFamilySparseExponentSplit p J q).2) := by
  apply Prod.ext
  · apply Finsupp.ext
    intro j
    change (powerRootExponentSplit p hp (powerRootNatExponent p hp (d j) + q j)).2 =
      (powerRootExponentSplit p hp (q j)).2
    have h := powerRootExponentSplit_nat_add p hp (d j) (q j)
    have h' := congrArg (fun z : ℕ × F => z.2) h
    exact h'
  · apply Finsupp.ext
    intro j
    exact congrArg Prod.fst (powerRootExponentSplit_nat_add p hp (d j) (q j))

end SerrePositivity.BhattScholze.Semiperfectoid

end

/-! ## RootFamilySparseBasis -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type v)
local notation "G" => powerRootExponentMonoid p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "F" => PowerRootFraction p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "B" => rootFamilyRaw p R J

/-- 小数部分ごとに通常多項式を並べる係数環上の線形同型。 -/
def rootFamilySparseFractionCoordinates : B ≃ₗ[R] ((J →₀ F) →₀ MvPolynomial J R) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.domLCongr (rootFamilySparseExponentSplit p J)).trans
      ((Finsupp.curryLinearEquiv R).trans
        (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv R).symm)))

/-- 単項式の座標は、小数指数成分に置いた整数指数の通常単項式。 -/
theorem rootFamilySparseFractionCoordinates_single (q : J →₀ G) (a : R) :
    rootFamilySparseFractionCoordinates p R J (AddMonoidAlgebra.single q a) =
      Finsupp.single (rootFamilySparseExponentSplit p J q).1
        (MvPolynomial.monomial (rootFamilySparseExponentSplit p J q).2 a) := by
  simp [rootFamilySparseFractionCoordinates, Finsupp.curry_single]
  rfl

/-- 任意添字の通常単項式は整数指数の根付き単項式へ送られる。 -/
theorem rootFamilyPolynomialMap_monomial_general (d : J →₀ ℕ) (a : R) :
    rootFamilyPolynomialMap p R J (MvPolynomial.monomial d a) =
      AddMonoidAlgebra.single (rootFamilyNatExponent p J d) a :=
  AddMonoidAlgebra.mapDomain_single

/-- 小数指数座標は通常多項式環の作用と両立する。 -/
theorem rootFamilySparseFractionCoordinates_smul :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    ∀ (f : MvPolynomial J R) (x : B),
      rootFamilySparseFractionCoordinates p R J (f • x) = f • rootFamilySparseFractionCoordinates p R J x := by
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
          change rootFamilySparseFractionCoordinates p R J
            ((MvPolynomial.monomial d a) • AddMonoidAlgebra.ofCoeff v) =
              (MvPolynomial.monomial d a) • rootFamilySparseFractionCoordinates p R J (AddMonoidAlgebra.ofCoeff v) at hv
          change rootFamilySparseFractionCoordinates p R J
            ((MvPolynomial.monomial d a) • AddMonoidAlgebra.ofCoeff w) =
              (MvPolynomial.monomial d a) • rootFamilySparseFractionCoordinates p R J (AddMonoidAlgebra.ofCoeff w) at hw
          change rootFamilySparseFractionCoordinates p R J
            ((MvPolynomial.monomial d a) •
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)) =
              (MvPolynomial.monomial d a) • rootFamilySparseFractionCoordinates p R J
                (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)
          rw [smul_add, map_add, hv, hw, map_add, smul_add]
      | single q b =>
          change rootFamilySparseFractionCoordinates p R J
            (rootFamilyPolynomialMap p R J (MvPolynomial.monomial d a) *
              AddMonoidAlgebra.single q b) =
              (MvPolynomial.monomial d a) • rootFamilySparseFractionCoordinates p R J
                (AddMonoidAlgebra.single q b)
          rw [rootFamilyPolynomialMap_monomial_general, AddMonoidAlgebra.single_mul_single,
            rootFamilySparseFractionCoordinates_single, rootFamilySparseFractionCoordinates_single,
            rootFamilySparseExponentSplit_nat_add]
          simp [Finsupp.smul_single, smul_eq_mul, MvPolynomial.monomial_mul_monomial]

/-- 概要：小数指数座標は通常多項式環上でも線形同型。
方針：係数環上の座標同型へ検証した作用の保存を加える。
規約：BS 著者版 Proposition 7.10 の完備化前。使われ方：正則列と商の評価。 -/
def rootFamilySparseFractionLinearEquiv :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    B ≃ₗ[MvPolynomial J R] ((J →₀ F) →₀ MvPolynomial J R) := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  exact { (rootFamilySparseFractionCoordinates p R J).toAddEquiv with
    map_smul' := rootFamilySparseFractionCoordinates_smul p R J }

/-- 小数指数は通常多項式環上の実際の自由基底を与える。 -/
def rootFamilySparseFractionBasis :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    Module.Basis (J →₀ F) (MvPolynomial J R) B := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  exact Module.Basis.ofRepr (rootFamilySparseFractionLinearEquiv p R J)

end SerrePositivity.BhattScholze.Semiperfectoid

end
