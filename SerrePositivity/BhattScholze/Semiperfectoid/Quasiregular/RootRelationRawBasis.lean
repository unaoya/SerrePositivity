module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyFractionBasis
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 生の有限根関係商の自由基底

## 概要
完備化前の根付き変数環を Xi−fi で割った環は、係数環上で自由かつ忠実平坦。
## 方針
小数指数基底を通常多項式の評価商へ基底変更する。
## 規約
BS 著者版 Proposition 7.10 の有限 T の生の模型。零係数環も含む。
## 使われ方
実完備化の純性、有界ねじれ、完備な関係商との比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
local notation "B" => rootFamilyRaw p R (Fin r)
local notation "S" => MvPolynomial (Fin r) R
local notation "I" => rootRelationPolynomialIdeal R f
local notation "F" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootFraction p (Nat.Prime.pos (Fact.out : p.Prime))

/-- 初期関係を生の根付き変数環へ写したイデアル。 -/
def rootRelationRawIdeal : Ideal B := (I).map (rootFamilyPolynomialMap p R (Fin r))

/-- 完備化前の有限根関係商。 -/
abbrev rootRelationRaw := B ⧸ rootRelationRawIdeal p R f

/-- 多項式の係数は生の根付き変数環でも同じ係数である。 -/
theorem rootFamilyPolynomialMap_C (a : R) :
    rootFamilyPolynomialMap p R (Fin r) (MvPolynomial.C a) = algebraMap R B a := by
  change AddMonoidAlgebra.mapDomain (rootFamilyNatExponent p (Fin r))
    (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

/-- 評価商を経由する作用は、元の R 作用と両立する。 -/
theorem rootRelationRaw_isScalarTower :
    letI : Algebra S B := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
    letI : Algebra (S ⧸ I) (rootRelationRaw p R f) := adicQuotientAlgebra I B
    IsScalarTower R (S ⧸ I) (rootRelationRaw p R f) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationRaw p R f) := adicQuotientAlgebra I B
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change Ideal.Quotient.mk _ (algebraMap R B a) =
    Ideal.Quotient.mk _ (rootFamilyPolynomialMap p R (Fin r) (MvPolynomial.C a))
  exact congrArg (Ideal.Quotient.mk _) (rootFamilyPolynomialMap_C p R a).symm

/-- 小数指数の基底を通常多項式の評価商へ移した基底。 -/
def rootRelationRawFractionBasis :
    letI : Algebra S B := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
    letI : Algebra (S ⧸ I) (rootRelationRaw p R f) := adicQuotientAlgebra I B
    Module.Basis (Fin r → F) (S ⧸ I) (rootRelationRaw p R f) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationRaw p R f) := adicQuotientAlgebra I B
  exact ((rootFamilyFractionBasis p R (Fin r)).baseChange (S ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

/-- 評価商の係数環上の単位基底と小数指数基底を合成した実基底。 -/
def rootRelationRawBasis : Module.Basis (PUnit.{1} × (Fin r → F)) R (rootRelationRaw p R f) := by
  letI : Algebra S B := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
  letI : Algebra (S ⧸ I) (rootRelationRaw p R f) := adicQuotientAlgebra I B
  letI := rootRelationRaw_isScalarTower p R f
  let b : Module.Basis PUnit.{1} R (S ⧸ I) :=
    (Module.Basis.singleton PUnit.{1} R).map (rootRelationPolynomialQuotientEquiv R f).symm.toLinearEquiv
  exact b.smulTower (rootRelationRawFractionBasis p R f)

/-- 生の有限根関係商は係数環上で自由。 -/
theorem rootRelationRaw_free : Module.Free R (rootRelationRaw p R f) :=
  Module.Free.of_basis (rootRelationRawBasis p R f)

/-- 生の有限根関係商は係数環上で忠実平坦。 -/
theorem rootRelationRaw_faithfullyFlat : Module.FaithfullyFlat R (rootRelationRaw p R f) := by
  letI := rootRelationRaw_free p R f
  rcases subsingleton_or_nontrivial R with hs | hn
  · letI := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    exact ⟨inferInstance, fun N _ _ _ => Module.subsingleton R N⟩
  · letI := hn
    let a0 : F := ⟨0, by norm_num⟩
    letI : Nonempty (PUnit.{1} × (Fin r → F)) := ⟨(PUnit.unit, fun _ => a0)⟩
    let b := rootRelationRawBasis p R f
    letI : Nontrivial (rootRelationRaw p R f) := b.repr.symm.injective.nontrivial
    infer_instance

/-- 概要：有限根関係商の p 冪ねじれの指数は係数環の指数で抑えられる。
方針：実基底の各座標に入力のねじれの評価を使う。
規約：BS 著者版 Proposition 7.10 の完備化前。
使われ方：T の実完備化へ渡す有界性。 -/
theorem rootRelationRaw_torsion_bound (N : ℕ)
    (hR : ∀ n : ℕ, ∀ x : R, (p : R)^n * x = 0 → (p : R)^N * x = 0)
    (n : ℕ) (x : rootRelationRaw p R f) (hx : (p : rootRelationRaw p R f)^n * x = 0) :
    (p : rootRelationRaw p R f)^N * x = 0 := by
  let e := (rootRelationRawBasis p R f).repr
  have h : (p : R)^n • x = 0 := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hx
  have hz : (p : R)^N • x = 0 := by
    apply e.injective
    apply Finsupp.ext
    intro i
    have he := congrArg (fun y => e y i) h
    have he' : (p : R)^n * e x i = 0 := by
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] using he
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]
      using hR n (e x i) he'
  simpa only [Algebra.smul_def, map_pow, map_natCast] using hz

end SerrePositivity.BhattScholze.Semiperfectoid
