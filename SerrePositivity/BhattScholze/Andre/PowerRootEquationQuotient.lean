module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialCoordinates

/-!
# André E1・E2：無限根の方程式商の入力射

## 概要

通常の商 R[Y^(1/p^∞)]/(f(Y)) からの環射は、係数射と f を消す互換根列で一意に決まる。
BS Rem 7.15（著者版 p.62）の完備入力環 S に接続するための未完備入力環。

## 方針

具体的な無限根多項式の評価射を主イデアルで降下し、係数と根による外延性を使う。
原典の記述を補う、単項式表示と通常の商の普遍性による経路。

## 規約

この段階は通常の商だけを扱う。完備化や原典の S との同定は主張しない。
モニック性・正次数・素数性は不要で、p の正値性だけを要求する。

## 使われ方

prismatic envelope の試験データを、個別の根列から実際の入力環の射へ変換する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
local notation "P" => PowerRootPolynomial R p hp
local notation "I" => Ideal.span {powerRootPolynomialBaseMap R p hp f}

/-- 概要：無限根多項式環を f(Y) = 0 で割った通常の入力環。
方針：第零変数での多項式評価が生成する主イデアルで割る。
規約：完備化をまだ施さず、モニック性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の S への未完備入力。 -/
abbrev PowerRootEquationQuotient := P ⧸ I

/-- 概要：方程式商への係数環の標準射。
方針：無限根多項式環の係数射と商射を合成する。
規約：商上の algebra インスタンスの選択を必要としない環射。
使われ方：BS Rem 7.15（著者版 p.62）の基底射を保つ入力データ。 -/
def powerRootEquationQuotientCoeff : R →+* PowerRootEquationQuotient p hp f :=
  (Ideal.Quotient.mk I).comp (algebraMap R P)

/-- 概要：方程式商内の全ての標準根変数。
方針：各 Yₙ を商射で写す。
規約：第零根が f の根になる。
使われ方：BS Rem 7.15（著者版 p.62）の根列の標準入力。 -/
def powerRootEquationQuotientRoot (n : ℕ) : PowerRootEquationQuotient p hp f :=
  Ideal.Quotient.mk I (powerRootPolynomialVariable R p hp n)

/-- 概要：方程式商の標準根列は p 冪について互換。
方針：無限根多項式環の関係式を商射で写す。
規約：任意の係数環を許す。
使われ方：BS Rem 7.15（著者版 p.62）の試験射からの根列抽出。 -/
theorem powerRootEquationQuotientRoot_pow (n : ℕ) :
    powerRootEquationQuotientRoot p hp f (n + 1) ^ p = powerRootEquationQuotientRoot p hp f n := by
  unfold powerRootEquationQuotientRoot
  rw [← map_pow, powerRootPolynomialVariable_pow]

/-- 概要：方程式商の第零根は指定された f を消す。
方針：評価と商射の可換性から主イデアルの生成元の消滅に帰着する。
規約：定数多項式を含めて成り立つ。
使われ方：BS Rem 7.15（著者版 p.62）の入力環内の方程式。 -/
theorem powerRootEquationQuotientRoot_equation :
    f.eval₂ (powerRootEquationQuotientCoeff p hp f)
      (powerRootEquationQuotientRoot p hp f 0) = 0 := by
  have h := Polynomial.hom_eval₂ f (algebraMap R P) (Ideal.Quotient.mk I)
    (powerRootPolynomialVariable R p hp 0)
  unfold powerRootEquationQuotientCoeff powerRootEquationQuotientRoot
  rw [← h]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

variable {B : Type v} [CommRing B]

/-- 概要：方程式商からの環射は係数と全根の像で決まる。
方針：商射で引き戻し、無限根多項式環の外延性を適用する。
規約：終域には完備性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の入力射の一意性。 -/
theorem powerRootEquationQuotient_ringHom_ext (F G : PowerRootEquationQuotient p hp f →+* B)
    (hc : F.comp (powerRootEquationQuotientCoeff p hp f) =
      G.comp (powerRootEquationQuotientCoeff p hp f))
    (hr : ∀ n, F (powerRootEquationQuotientRoot p hp f n) =
      G (powerRootEquationQuotientRoot p hp f n)) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  exact powerRootPolynomial_ringHom_ext p hp _ _ hc hr

/-- 概要：f を消す互換根列と係数射は方程式商からの一意な環射を与える。
方針：無限根評価射を生成元が消える主イデアルで降下し、外延性で一意性を得る。
規約：全ての根を同時に保存し、終域の正則性や完備性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の根データと入力射の具体的な対応。 -/
theorem existsUnique_powerRootEquationQuotientHom (k : R →+* B)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (hf : f.eval₂ k (ρ 0) = 0) :
    ∃! F : PowerRootEquationQuotient p hp f →+* B,
      F.comp (powerRootEquationQuotientCoeff p hp f) = k ∧
        ∀ n, F (powerRootEquationQuotientRoot p hp f n) = ρ n := by
  let g := powerRootPolynomialEval p hp k ρ hρ
  have heval : g (powerRootPolynomialBaseMap R p hp f) = 0 := by
    unfold powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, powerRootPolynomialEval_variable]
    have hc : g.comp (algebraMap R P) = k := by
      apply RingHom.ext
      exact powerRootPolynomialEval_coeff p hp k ρ hρ
    rw [hc]
    exact hf
  let F : PowerRootEquationQuotient p hp f →+* B := Ideal.Quotient.lift I g (by
    change I ≤ RingHom.ker g
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact heval)
  have hc : F.comp (powerRootEquationQuotientCoeff p hp f) = k := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp k ρ hρ
  have hr : ∀ n, F (powerRootEquationQuotientRoot p hp f n) = ρ n :=
    powerRootPolynomialEval_variable p hp k ρ hρ
  refine ⟨F, ⟨hc, hr⟩, ?_⟩
  intro K hK
  exact powerRootEquationQuotient_ringHom_ext p hp f K F (hK.1.trans hc.symm)
    (fun n => (hK.2 n).trans (hr n).symm)

end SerrePositivity.BhattScholze.Andre
