module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilySparseBasis
public import SerrePositivity.CommutativeAlgebra.PolynomialSubsetQuotient

/-!
# 任意初期根関係の自由基底と座標

## 概要
任意の初期変数部分族の生の商の自由基底、共通ねじれ指数と完備基底上の座標を与える。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## RootRelationSubsetRaw -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u) (s : Set J)
local notation "B" => rootFamilyRaw p R J
local notation "S" => MvPolynomial J R
local notation "I" => polynomialSubsetIdeal R J s
local notation "F" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootFraction p (Nat.Prime.pos (Fact.out : p.Prime))

/-- 指定した初期変数の関係イデアル。 -/
def rootRelationSubsetRawIdeal : Ideal B := (I).map (rootFamilyPolynomialMap p R J)

/-- 指定した初期変数のみを零にした、生の根付き環。 -/
abbrev rootRelationSubsetRaw := B ⧸ rootRelationSubsetRawIdeal p R J s

/-- 多項式の係数は生の根付き変数環でも同じ係数である。 -/
theorem rootFamilyPolynomialMap_coeff (a : R) :
    rootFamilyPolynomialMap p R J (MvPolynomial.C a) = algebraMap R B a := by
  change AddMonoidAlgebra.mapDomain (rootFamilyNatExponent p J)
    (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

/-- 評価商を経由する作用は、元の R 作用と両立する。 -/
theorem rootRelationSubsetRaw_isScalarTower :
    letI : Algebra S B := (rootFamilyPolynomialMap p R J).toAlgebra
    letI : Algebra (S ⧸ I) (rootRelationSubsetRaw p R J s) := adicQuotientAlgebra I B
    IsScalarTower R (S ⧸ I) (rootRelationSubsetRaw p R J s) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R J).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationSubsetRaw p R J s) := adicQuotientAlgebra I B
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change Ideal.Quotient.mk _ (algebraMap R B a) =
    Ideal.Quotient.mk _ (rootFamilyPolynomialMap p R J (MvPolynomial.C a))
  exact congrArg (Ideal.Quotient.mk _) (rootFamilyPolynomialMap_coeff p R J a).symm

/-- 小数指数の基底を通常多項式の評価商へ移した基底。 -/
def rootRelationSubsetRawFractionBasis :
    letI : Algebra S B := (rootFamilyPolynomialMap p R J).toAlgebra
    letI : Algebra (S ⧸ I) (rootRelationSubsetRaw p R J s) := adicQuotientAlgebra I B
    Module.Basis (J →₀ F) (S ⧸ I) (rootRelationSubsetRaw p R J s) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R J).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationSubsetRaw p R J s) := adicQuotientAlgebra I B
  exact ((rootFamilySparseFractionBasis p R J).baseChange (S ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

/-- 評価商の係数環上の単位基底と小数指数基底を合成した実基底。 -/
def rootRelationSubsetRawBasis : Module.Basis (({j // j ∉ s} →₀ ℕ) × (J →₀ F)) R (rootRelationSubsetRaw p R J s) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R J).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationSubsetRaw p R J s) := adicQuotientAlgebra I B
  letI := rootRelationSubsetRaw_isScalarTower p R J s
  let b : Module.Basis ({j // j ∉ s} →₀ ℕ) R (S ⧸ I) :=
    (MvPolynomial.basisMonomials _ _).map (polynomialSubsetQuotientEquiv R J s).symm.toLinearEquiv
  exact b.smulTower (rootRelationSubsetRawFractionBasis p R J s)

/-- 概要：有限根関係商の p 冪ねじれの指数は係数環の指数で抑えられる。
方針：実基底の各座標に入力のねじれの評価を使う。
規約：BS 著者版 Proposition 7.10 の完備化前。
使われ方：T の実完備化へ渡す有界性。 -/
theorem rootRelationSubsetRaw_torsion_bound (N : ℕ)
    (hR : ∀ n : ℕ, ∀ x : R, (p : R) ^n * x = 0 → (p : R) ^N * x = 0)
    (n : ℕ) (x : rootRelationSubsetRaw p R J s) (hx : (p : rootRelationSubsetRaw p R J s) ^n * x = 0) :
    (p : rootRelationSubsetRaw p R J s) ^N * x = 0 := by
  let e := (rootRelationSubsetRawBasis p R J s).repr
  have h : (p : R) ^n • x = 0 := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hx
  have hz : (p : R) ^N • x = 0 := by
    apply e.injective
    apply Finsupp.ext
    intro i
    have he := congrArg (fun y => e y i) h
    have he' : (p : R) ^n * e x i = 0 := by
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] using he
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]
      using hR n (e x i) he'
  simpa only [Algebra.smul_def, map_pow, map_natCast] using hz

end SerrePositivity.BhattScholze.Semiperfectoid

end

/-! ## RootRelationSubsetCoordinates -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)

/-- 初期関係イデアルを完備な根付き基底へ送ったイデアル。 -/
@[expose] def rootRelationSubsetBaseIdeal (s : Set J) : Ideal (rootFamilyBase p R J) :=
  (rootRelationSubsetRawIdeal p R J s).map (rootFamilyUnit p R J)

/-- 任意添字の多項式変数の像は第零段の根付き単項式。 -/
theorem rootFamilyPolynomialMap_X_general (i : J) :
    rootFamilyPolynomialMap p R J (MvPolynomial.X i) =
      AddMonoidAlgebra.single
        (Finsupp.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p (Nat.Prime.pos (Fact.out : p.Prime)) 0)) 1 := by
  change AddMonoidAlgebra.mapDomain (rootFamilyNatExponent p J)
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  apply Finsupp.ext
  intro j
  classical
  by_cases h : i = j
  · subst j
    simp [rootFamilyNatExponent, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent]
  · simp [rootFamilyNatExponent, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h),
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent]

/-- 任意初期関係の完備基底上のイデアルは、対応する第零段の根で生成される。 -/
theorem rootRelationSubsetBaseIdeal_eq (s : Set J) :
    rootRelationSubsetBaseIdeal p R J s = Ideal.span ((fun j => rootFamilyVariable p R J j 0) '' s) := by
  rw [rootRelationSubsetBaseIdeal, rootRelationSubsetRawIdeal, polynomialSubsetIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro i _
  rw [rootFamilyPolynomialMap_X_general]
  rfl

/-- 全初期関係の場合、イデアルは各変数の第零段の根の生成イデアル。 -/
theorem rootRelationSubsetBaseIdeal_univ :
    rootRelationSubsetBaseIdeal p R J Set.univ =
      Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0) := by
  rw [rootRelationSubsetBaseIdeal_eq, Set.image_univ]

end SerrePositivity.BhattScholze.Semiperfectoid

end
