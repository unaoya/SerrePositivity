module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialPerfectDelta
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialCoordinates

/-!
# André E1・E2：係数 Frobenius と指数 Frobenius の分離

## 概要

完全 δ 係数環上の無限根環の Frobenius は、係数 Frobenius と指数 p 倍の
互いに可換な二つの δ 自己同型の合成。
BS Rem 7.15（著者版 p.62）の φ_A による係数変更と変数の作用を区別する。

## 方針

モノイド環の係数同型と指数同型を別々に束ね、可換性を既存の写像の自然性で示す。
p 正則性の下で Frobenius との可換性から δ 射であることを得る。

## 規約

係数同型は全根変数を固定し、指数同型は係数を固定する。未完備の環を扱う。

## 使われ方

prismatic envelope の raw 包の係数変更を、入力多項式と変数を追跡して比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
variable (D : DeltaStructure p A) (hD : D.IsPerfect)

/-- 概要：係数 Frobenius のみを適用する無限根環の環同型。
方針：係数環同型を加法モノイド環へ持ち上げる。
規約：単項式の指数は固定する。
使われ方：BS Rem 7.15（著者版 p.62）の φ_A による係数作用。 -/
def powerRootCoefficientFrobeniusEquiv : P ≃+* P :=
  AddMonoidAlgebra.mapRingEquiv G (D.frobeniusEquiv hD)

/-- 概要：指数の p 倍のみを適用する無限根環の環同型。
方針：指数加法同型をモノイド環へ持ち上げる。
規約：係数を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の全体 Frobenius の変数成分。 -/
def powerRootVariableFrobeniusEquiv : P ≃+* P :=
  AddMonoidAlgebra.mapDomainRingEquiv A (powerRootExponentPrimeScaleEquiv p)

/-- 概要：係数 Frobenius は単項式の係数だけを送る。
方針：係数環同型の単項式公式を使う。
規約：任意の指数・係数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数と変数の分離。 -/
theorem powerRootCoefficientFrobeniusEquiv_single (q : G) (b : A) :
    powerRootCoefficientFrobeniusEquiv p D hD (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (D.frobeniusLift b) :=
  AddMonoidAlgebra.mapRingEquiv_single _ _ _

/-- 概要：指数 Frobenius は単項式の指数だけを p 倍する。
方針：指数同型の単項式公式を使う。
規約：係数は同じ元を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の指数作用。 -/
theorem powerRootVariableFrobeniusEquiv_single (q : G) (b : A) :
    powerRootVariableFrobeniusEquiv (A := A) p (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single (p • q) b :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

/-- 概要：係数 Frobenius は元の係数の標準像をその Frobenius 像へ送る。
方針：零指数の単項式で計算する。
規約：標準係数射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の照合。 -/
theorem powerRootCoefficientFrobeniusEquiv_coeff (b : A) :
    powerRootCoefficientFrobeniusEquiv p D hD (algebraMap A P b) =
      algebraMap A P (D.frobeniusLift b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientFrobeniusEquiv_single p D hD 0 b

/-- 概要：係数 Frobenius は全ての根変数を固定する。
方針：係数 1 の単項式で計算する。
規約：全ての段 n を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の入力多項式の係数変更。 -/
theorem powerRootCoefficientFrobeniusEquiv_variable (n : ℕ) :
    powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientFrobeniusEquiv_single, map_one]

/-- 概要：指数 Frobenius は元の係数の標準像を固定する。
方針：零指数の単項式で計算する。
規約：係数環 A の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の A 線形な変数作用。 -/
theorem powerRootVariableFrobeniusEquiv_coeff (b : A) :
    powerRootVariableFrobeniusEquiv (A := A) p (algebraMap A P b) = algebraMap A P b := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootVariableFrobeniusEquiv_single p (0 : G) b

/-- 概要：指数 Frobenius は各根変数をその p 乗へ送る。
方針：単項式の冪と指数 p 倍の公式を使う。
規約：全ての段 n を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の変数の再配置。 -/
theorem powerRootVariableFrobeniusEquiv_variable (n : ℕ) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n ^ p := by
  simp only [powerRootPolynomialVariable, powerRootVariableFrobeniusEquiv_single,
    AddMonoidAlgebra.single_pow, one_pow]

/-- 概要：係数と指数の Frobenius は環射として可換。
方針：モノイド環の係数写像と指数写像の自然性を使う。
規約：両側の合成順序を環射の等式で明示する。
使われ方：BS Rem 7.15（著者版 p.62）の δ 互換性の判定。 -/
theorem powerRootFrobeniusFactors_commute :
    (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom.comp
      (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom =
    (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom.comp
      (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom :=
  AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom D.frobeniusLift (powerRootExponentPrimeScale p)

/-- 概要：全体 Frobenius は係数成分の後に指数成分を適用したもの。
方針：既存の標準 Frobenius の定義を使う。
規約：既存 δ 構造の Frobenius を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の二つの作用の正確な関係。 -/
theorem powerRootFrobeniusFactors_apply (t : P) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootCoefficientFrobeniusEquiv p D hD t) =
      powerRootPolynomialFrobenius p D t := rfl

/-- 概要：係数 Frobenius 成分は標準無限根 δ 構造の δ 自己同型。
方針：全体 Frobenius との可換性を p 正則性の下で δ 互換性に戻す。
規約：既存の δ 構造を使う。
使われ方：BS Rem 7.15（著者版 p.62）の係数変更を raw δ 包へ適用する入力。 -/
theorem powerRootCoefficientFrobeniusEquiv_isDeltaHom :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsDeltaHom
      (powerRootPolynomialDelta p hD.p_mul_injective D)
      (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (powerRootPolynomial_primeRegular p hD.p_mul_injective)
  intro t
  rw [powerRootPolynomialDelta_frobenius]
  exact RingHom.congr_fun (powerRootFrobeniusFactors_commute p D hD)
    (powerRootCoefficientFrobeniusEquiv p D hD t)

/-- 概要：指数 Frobenius 成分も標準無限根 δ 構造の δ 自己同型。
方針：係数成分との可換性を全体 Frobenius との可換性にし、p 正則性を使う。
規約：係数環の完全性から p 正則性を供給する。
使われ方：BS Rem 7.15（著者版 p.62）の変数成分を raw δ 包へ適用する入力。 -/
theorem powerRootVariableFrobeniusEquiv_isDeltaHom :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsDeltaHom
      (powerRootPolynomialDelta p hD.p_mul_injective D)
      (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (powerRootPolynomial_primeRegular p hD.p_mul_injective)
  intro t
  rw [powerRootPolynomialDelta_frobenius]
  exact congrArg (powerRootVariableFrobeniusEquiv (A := A) p)
    (RingHom.congr_fun (powerRootFrobeniusFactors_commute p D hD) t).symm

/-- 概要：係数 Frobenius は通常多項式の係数だけを Frobenius で送って評価する。
方針：評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の φ_A 係数変更後の f の追跡。 -/
theorem powerRootCoefficientFrobeniusEquiv_baseMap (f : Polynomial A) :
    powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap A p hp (f.map D.frobeniusLift) := by
  unfold powerRootPolynomialBaseMap
  change (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom
    (Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _
    (powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialVariable A p hp 0)) f = _
  rw [powerRootCoefficientFrobeniusEquiv_variable, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientFrobeniusEquiv_coeff p D hD b

/-- 概要：二成分の合成同型は既存 δ 構造の Frobenius 同型そのもの。
方針：各元上で全体 Frobenius と一致することを使い環同型の外延性を適用する。
規約：完全性証明は既存の無限根 δ 完全性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の係数成分と以前の全体比較の接続。 -/
theorem powerRootFrobeniusFactors_equiv :
    (powerRootCoefficientFrobeniusEquiv p D hD).trans
      (powerRootVariableFrobeniusEquiv (A := A) p) =
    (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusEquiv
      (powerRootPolynomialDelta_isPerfect p D hD) := by
  apply RingEquiv.ext
  intro t
  change powerRootVariableFrobeniusEquiv (A := A) p
    (powerRootCoefficientFrobeniusEquiv p D hD t) =
      (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusLift t
  rw [powerRootPolynomialDelta_frobenius]
  exact powerRootFrobeniusFactors_apply p D hD t

/-- 概要：指数成分は通常多項式の係数を保ち、通常変数だけを p 乗にする。
方針：多項式評価の自然性と係数・変数の計算公式を使う。
規約：任意の多項式を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数引戻し後の変数再配置。 -/
theorem powerRootVariableFrobeniusEquiv_baseMap (f : Polynomial A) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialBaseMap A p hp f) =
      Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0 ^ p) f := by
  unfold powerRootPolynomialBaseMap
  change (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom
    (Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _
    (powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialVariable A p hp 0)) f = _
  rw [powerRootVariableFrobeniusEquiv_variable]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootVariableFrobeniusEquiv_coeff p b

end SerrePositivity.BhattScholze.Andre
