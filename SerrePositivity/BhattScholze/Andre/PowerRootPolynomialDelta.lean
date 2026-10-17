module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomial
public import SerrePositivity.BhattScholze.DeltaFrobenius
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# André E1・E2：無限 p 冪根多項式環の δ 構造

## 概要

p 正則な δ 係数環上で、無限 p 冪根多項式環に全根変数が rank 1 となる δ 構造を与える。
BS Rem 7.15（著者版 p.62）の無限根変数への実 pd 計算の準備。

## 方針

単項式の指数を p 倍し係数に元の Frobenius を作用させる環射を構成する。
mod p で通常の p 乗と一致することを加法モノイド環の帰納法で証明し、
p 正則環の Frobenius 持ち上げから δ 構造を得る。

## 規約

係数環の p 正則性を明示する。元の無限根多項式環の台環を変更しない。
p 進完備化や prismatic envelope との同定はこのファイルに含まない。

## 使われ方

無限 p 冪根多項式環上のモニック入力に実 mod p 分冪包の構成を適用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp

/-- 概要：無限根指数の p 倍を取る加法モノイド射。
方針：自然数倍の加法保存性を使う。
規約：指数は同じ p 冪分母の非負有理数型に属する。
使われ方：BS Rem 7.15（著者版 p.62）の単項式 Frobenius。 -/
def powerRootExponentPrimeScale : G →+ G where
  toFun q := p • q
  map_zero' := nsmul_zero p
  map_add' x y := nsmul_add x y p

/-- 概要：係数 Frobenius と指数 p 倍による無限根多項式環の環自己射。
方針：モノイド環の係数写像と指数写像を合成する。
規約：通常の p 乗写像とは mod p で比較する。
使われ方：BS Rem 7.15（著者版 p.62）の δ 構造の Frobenius 持ち上げ。 -/
def powerRootPolynomialFrobenius (D : DeltaStructure p A) : P →+* P :=
  (AddMonoidAlgebra.mapDomainRingHom A (powerRootExponentPrimeScale p)).comp
    (AddMonoidAlgebra.mapRingHom G D.frobeniusLift)

/-- 概要：単項式の Frobenius は係数 Frobenius と指数 p 倍を取る。
方針：係数写像と指数写像の単項式公式を使う。
規約：任意の係数と指数について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の根変数の rank 1 性。 -/
theorem powerRootPolynomialFrobenius_single (D : DeltaStructure p A) (q : G) (a : A) :
    powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single q a) =
      AddMonoidAlgebra.single (p • q) (D.frobeniusLift a) := by
  change AddMonoidAlgebra.mapDomain (powerRootExponentPrimeScale p)
    (AddMonoidAlgebra.mapRingHom G D.frobeniusLift (AddMonoidAlgebra.single q a)) = _
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- 概要：無限根多項式の Frobenius は係数上で元の Frobenius を延長する。
方針：零指数の単項式として係数を計算する。
規約：元の標準係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の基底 δ 構造との整合性。 -/
theorem powerRootPolynomialFrobenius_coeff (D : DeltaStructure p A) (a : A) :
    powerRootPolynomialFrobenius p D (algebraMap A P a) = algebraMap A P (D.frobeniusLift a) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootPolynomialFrobenius_single p D (0 : G) a

/-- 概要：係数環の p 正則性は無限根多項式環へ移る。
方針：単項式基底による自由性と平坦性を使う。
規約：係数環の非零性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の δ 構造の存在への入力。 -/
theorem powerRootPolynomial_primeRegular
    (hpA : Function.Injective (fun a : A => (p : A) * a)) :
    Function.Injective (fun a : P => (p : P) * a) := by
  let := powerRootPolynomial_free A p hp
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)

/-- 概要：構成した Frobenius は実 mod p 商で通常の p 乗に一致する。
方針：単項式・加法・係数倍の帰納法と、素数 p の二項係数公式を使う。
規約：零係数環も含め、CharP インスタンスを要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 持ち上げからの δ 構造。 -/
theorem powerRootPolynomialFrobenius_mod_prime (D : DeltaStructure p A) (x : P) :
    Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialFrobenius p D x) =
      Ideal.Quotient.mk (Ideal.span {(p : P)}) x ^ p := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : P)})
  have hpQ : (p : P ⧸ Ideal.span {(p : P)}) = 0 := by
    change q (p : P) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hcoeff (a : A) : q (powerRootPolynomialFrobenius p D (algebraMap A P a)) =
      q (algebraMap A P a) ^ p := by
    rw [powerRootPolynomialFrobenius_coeff, D.frobeniusLift_apply]
    simp only [map_add, map_mul, map_natCast, map_pow, hpQ, zero_mul, add_zero]
  change q (powerRootPolynomialFrobenius p D x) = q x ^ p
  induction x using AddMonoidAlgebra.induction_on with
  | of t =>
    change q (powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single t 1)) =
      q (AddMonoidAlgebra.single t 1) ^ p
    rw [powerRootPolynomialFrobenius_single, map_one, ← map_pow,
      AddMonoidAlgebra.single_pow, one_pow]
  | add x z hx hz =>
    simp only [map_add, hx, hz]
    symm
    simpa only [hpQ, zero_mul, add_zero] using
      add_pow_prime_eq' (Fact.out : p.Prime) (q x) (q z)
  | smul a x hx =>
    rw [Algebra.smul_def]
    simp only [map_mul, hcoeff, hx, mul_pow]

/-- 概要：p 正則な係数環上では指定した無限根 Frobenius を持つ δ 構造が一意に存在する。
方針：自由性による p 正則性と実 mod p 一致を Frobenius 持ち上げの存在定理へ渡す。
規約：元の無限根多項式環の上で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の無限根変数の実 δ 持ち上げ。 -/
theorem existsUnique_powerRootPolynomialDelta
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    ∃! E : DeltaStructure p P, E.frobeniusLift = powerRootPolynomialFrobenius p D :=
  DeltaStructure.existsUnique_of_mod_p (powerRootPolynomial_primeRegular p hpA)
    (powerRootPolynomialFrobenius p D) (powerRootPolynomialFrobenius_mod_prime p D)

/-- 概要：係数 Frobenius と全無限根変数の rank 1 性を指定した δ 構造。
方針：一意存在した構造を選ぶ。
規約：p 正則性を明示し、ねじれを持つ係数環へ無条件に延長しない。
使われ方：BS Rem 7.15（著者版 p.62）の無限根多項式入力の分冪包。 -/
def powerRootPolynomialDelta
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    DeltaStructure p P :=
  Classical.choose (existsUnique_powerRootPolynomialDelta p hpA D)

/-- 概要：選んだ δ 構造の Frobenius は指定した単項式 Frobenius に一致する。
方針：一意存在の存在証人の性質を取り出す。
規約：元の係数環の Frobenius を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の係数と変数上の δ の計算。 -/
theorem powerRootPolynomialDelta_frobenius
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    (powerRootPolynomialDelta p hpA D).frobeniusLift = powerRootPolynomialFrobenius p D :=
  (Classical.choose_spec (existsUnique_powerRootPolynomialDelta p hpA D)).1


/-- 概要：各無限根変数の Frobenius はその p 乗。
方針：係数 1 の単項式上の指数 p 倍公式を使う。
規約：全ての段 n で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の全根変数の rank 1 性。 -/
theorem powerRootPolynomialFrobenius_variable (D : DeltaStructure p A) (n : ℕ) :
    powerRootPolynomialFrobenius p D (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n ^ p := by
  change powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single _ 1) =
    AddMonoidAlgebra.single _ 1 ^ p
  rw [powerRootPolynomialFrobenius_single, map_one, AddMonoidAlgebra.single_pow, one_pow]

/-- 概要：無限根多項式環への標準係数射は実 δ 射である。
方針：係数 Frobenius の互換性と終域の p 正則性から δ の互換性を得る。
規約：元の係数環の δ 構造を延長する。
使われ方：BS Rem 7.15（著者版 p.62）の係数側との整合性。 -/
theorem powerRootPolynomialDelta_coeff_isDeltaHom
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    D.IsDeltaHom (powerRootPolynomialDelta p hpA D) (algebraMap A P) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift (algebraMap A P)
    (powerRootPolynomial_primeRegular p hpA)
  intro a
  rw [powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_coeff]

/-- 概要：全無限根変数の δ は零。
方針：Frobenius が p 乗になる公式と δ の恒等式を比較し、p 正則性で消去する。
規約：任意の段 n を含む。
使われ方：BS Rem 7.15（著者版 p.62）の無限根変数の実 rank 1 δ 持ち上げ。 -/
theorem powerRootPolynomialDelta_variable
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) (n : ℕ) :
    (powerRootPolynomialDelta p hpA D).delta (powerRootPolynomialVariable A p hp n) = 0 := by
  apply powerRootPolynomial_primeRegular p hpA
  have he : (powerRootPolynomialDelta p hpA D).frobeniusLift
      (powerRootPolynomialVariable A p hp n) = powerRootPolynomialVariable A p hp n ^ p := by
    rw [powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_variable]
  have hδ := (powerRootPolynomialDelta p hpA D).frobeniusLift_apply
    (powerRootPolynomialVariable A p hp n)
  linear_combination he - hδ

end SerrePositivity.BhattScholze.Andre
