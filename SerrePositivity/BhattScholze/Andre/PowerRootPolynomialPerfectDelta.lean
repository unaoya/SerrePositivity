module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialDelta
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius
public import SerrePositivity.BhattScholze.Andre.DeltaDivisionCoefficientAut

/-!
# André E1・E2：無限根多項式環の完全 δ 構造

## 概要

完全 δ 係数環上の無限 p 冪根多項式環の標準 δ 構造は完全。
BS Rem 7.15（著者版 p.62）の Frobenius 引戻し比較の入力環を具体化する。

## 方針

指数の p 倍は同じ p 冪分母モノイドの加法同型であり、逆は有理数として p で割る。
この指数同型と係数 Frobenius 同型をモノイド環上で合成する。

## 規約

未完備の無限根環を扱う。p 進完備化や prismatic envelope の同定を含まない。

## 使われ方

原典の Frobenius による係数変更を、逆を持つ具体的な δ 環射として扱うための入口。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp

/-- 概要：無限根指数の p 倍は単射。
方針：有理数としての非零 p 倍を消去する。
規約：指数モノイドの部分型の等式として述べる。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius の単射性。 -/
theorem powerRootExponentPrimeScale_injective :
    Function.Injective (powerRootExponentPrimeScale p) := by
  intro q r h
  apply Subtype.ext
  have hv := congrArg (fun t : G => (t : ℚ)) h
  change (p : ℚ) * (q : ℚ) = (p : ℚ) * (r : ℚ) at hv
  exact mul_left_cancel₀ (by exact_mod_cast (hp).ne' : (p : ℚ) ≠ 0) hv

/-- 概要：無限根指数の p 倍は全射。
方針：q/p の分母条件を元の条件の一段先で確認する。
規約：分母表示の選択によらず有理数として q/p を持ち上げる。
使われ方：BS Rem 7.15（著者版 p.62）の逆 Frobenius の指数。 -/
theorem powerRootExponentPrimeScale_surjective :
    Function.Surjective (powerRootExponentPrimeScale p) := by
  intro q
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (hp).ne'
  have hmem : (q : ℚ) / (p : ℚ) ∈ powerRootExponentMonoid p hp := by
    obtain ⟨n, b, hb⟩ := q.property
    refine ⟨n + 1, b, ?_⟩
    rw [pow_succ]
    calc
      (q : ℚ) / p * ((p : ℚ) ^ n * p) = (q : ℚ) * (p : ℚ) ^ n := by
        field_simp
      _ = b := hb
  refine ⟨⟨(q : ℚ) / p, hmem⟩, ?_⟩
  apply Subtype.ext
  change (p : ℚ) * ((q : ℚ) / p) = (q : ℚ)
  exact mul_div_cancel₀ _ hpQ

/-- 概要：無限根指数の p 倍を加法同型として束ねる。
方針：同じ標準加法射の単射性と全射性を使う。
規約：順方向は p 倍のまま変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の単項式 Frobenius 同型。 -/
def powerRootExponentPrimeScaleEquiv : G ≃+ G :=
  AddEquiv.ofBijective (powerRootExponentPrimeScale p)
    ⟨powerRootExponentPrimeScale_injective p, powerRootExponentPrimeScale_surjective p⟩

variable {A : Type u} [CommRing A]
local notation "P" => PowerRootPolynomial A p hp

/-- 概要：完全係数環上の無限根環の標準 Frobenius は環同型。
方針：係数 Frobenius 同型と指数 p 倍の加法同型をモノイド環へ持ち上げて合成する。
規約：既存の標準 Frobenius と同じ順方向の射。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 引戻しの具体的な係数射。 -/
def powerRootPolynomialPerfectFrobeniusEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) :
    P ≃+* P :=
  (AddMonoidAlgebra.mapRingEquiv G (D.frobeniusEquiv hD)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv A (powerRootExponentPrimeScaleEquiv p))

/-- 概要：構成した Frobenius 同型の順射は既存の標準 Frobenius に一致。
方針：二つのモノイド環の標準写像の合成の定義を使う。
規約：δ 構造を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の δ 完全性の確認。 -/
theorem powerRootPolynomialPerfectFrobeniusEquiv_apply
    (D : DeltaStructure p A) (hD : D.IsPerfect) (t : P) :
    powerRootPolynomialPerfectFrobeniusEquiv p D hD t = powerRootPolynomialFrobenius p D t := rfl

/-- 概要：完全 δ 係数環上の無限根多項式環の標準 δ 構造は完全。
方針：標準 Frobenius を具体的環同型の順射と同定して全単射性を得る。
規約：係数環の p 正則性は完全性から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の無限根入力上の Frobenius 比較。 -/
theorem powerRootPolynomialDelta_isPerfect (D : DeltaStructure p A) (hD : D.IsPerfect) :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsPerfect := by
  change Function.Bijective (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusLift
  rw [powerRootPolynomialDelta_frobenius]
  exact (powerRootPolynomialPerfectFrobeniusEquiv p D hD).bijective

variable {σ : Type v}

/-- 概要：完全係数上の無限根環の raw 除算包は Frobenius 係数変更で環同型。
方針：無限根 δ 環の完全性から Frobenius 自己同型を作り、係数自己同型の一般計算を使う。
規約：a/d の包から φ(a)/φ(d) の包への向き。
使われ方：BS Rem 7.15（著者版 p.62）、Cor 2.39（p.25）の raw 比較の入力。 -/
def powerRootPolynomialDivisionFrobeniusEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    DeltaAdjoinDivision E d a ≃+*
      DeltaAdjoinDivision E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s)) :=
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  deltaDivisionCoefficientAutEquiv E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a

/-- 概要：raw Frobenius 比較は無限根環の係数を Frobenius で送る。
方針：係数自己同型による raw 同型の係数公式を使う。
規約：係数環は無限根入力環全体。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 引戻しの係数作用。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_coeff
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) (b : P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    powerRootPolynomialDivisionFrobeniusEquiv p D hD d a (deltaAdjoinDivisionMap E d a b) =
      deltaAdjoinDivisionMap E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s))
        (E.frobeniusLift b) := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_coeff E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a b

/-- 概要：raw Frobenius 比較は初期除算変数の添字を保つ。
方針：係数自己同型による同型の変数公式を使う。
規約：任意の入力族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）のモニック根関係の座標比較。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_variable
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) (s : σ) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    powerRootPolynomialDivisionFrobeniusEquiv p D hD d a
      (deltaAdjoinDivisionVariable E d a s) =
        deltaAdjoinDivisionVariable E (E.frobeniusLift d) (fun t => E.frobeniusLift (a t)) s := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_variable E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a s

/-- 概要：無限根環の raw Frobenius 比較は実 δ 射。
方針：一般の係数自己同型による比較の δ 互換性を供給する。
規約：完備化前の両商 δ 構造を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の比較への入力。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    (deltaAdjoinDivisionStructure E d a).IsDeltaHom
      (deltaAdjoinDivisionStructure E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s)))
      (powerRootPolynomialDivisionFrobeniusEquiv p D hD d a).toRingHom := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_isDeltaHom E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a

end SerrePositivity.BhattScholze.Andre
