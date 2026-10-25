module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootExponentEvaluation

/-!
# André E1・E2：具体的な無限根多項式環の普遍性

## 概要

任意の係数環射と互換な p 冪根列に対し、現在の単項式表示の無限根多項式環から
係数と全根を保つ環射が一意に存在する。BS Rem 7.15（著者版 p.62）の入力環。

## 方針

有理指数を根列で評価するモノイド射を加法モノイド環へ延長する。
一意性は各単項式が一つの有限段の根変数の冪になることから従う。
原典の記述を補う具体的な有理指数による経路。

## 規約

p の正値性だけを仮定し、終域の標数・正則性・完備性は制限しない。

## 使われ方

prismatic envelope の入力射を、根の像を指定するデータから作る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p)
variable {B : Type v} [CommRing B]
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限根多項式環の環射は係数と全根変数の像で決まる。
方針：単項式を一つの根変数の冪に表し、単項式による加法的生成を使う。
規約：終域には任意の可換環を許す。
使われ方：BS Rem 7.15（著者版 p.62）の入力射の一意性。 -/
theorem powerRootPolynomial_ringHom_ext (F G : P →+* B)
    (hcoeff : F.comp (algebraMap R P) = G.comp (algebraMap R P))
    (hroot : ∀ n, F (powerRootPolynomialVariable R p hp n) =
      G (powerRootPolynomialVariable R p hp n)) : F = G := by
  apply RingHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of q =>
    obtain ⟨n, k, h⟩ := powerRootPolynomial_single_exists R p hp q 1
    simp only [map_one, one_mul] at h
    change F (AddMonoidAlgebra.single q 1) = G (AddMonoidAlgebra.single q 1)
    rw [h, map_pow, map_pow, hroot]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul a x hx =>
    have ha : F (algebraMap R P a) = G (algebraMap R P a) := RingHom.congr_fun hcoeff a
    rw [Algebra.smul_def, map_mul, map_mul, ha, hx]

variable (f : R →+* B) (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)

/-- 概要：指定した互換根列への無限根多項式の評価射。
方針：指数のモノイド射と係数環射を加法モノイド環の普遍射へ渡す。
規約：元の具体的な無限根多項式環を源とする。
使われ方：BS Rem 7.15（著者版 p.62）の根データからの実入力射。 -/
def powerRootPolynomialEval : P →+* B :=
  AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ)
    (fun _ _ => Commute.all _ _)

/-- 概要：無限根評価射は元の係数を指定係数射へ送る。
方針：零指数の単項式を評価し、モノイド射の単位保存性を使う。
規約：全ての係数元を含む。
使われ方：BS Rem 7.15（著者版 p.62）の基底環上の普遍性。 -/
theorem powerRootPolynomialEval_coeff (a : R) :
    powerRootPolynomialEval p hp f ρ hρ (algebraMap R P a) = f a := by
  change AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ) _
    (AddMonoidAlgebra.single 0 a) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change f a * (powerRootExponentEvalHom p hp ρ hρ) 1 = f a
  rw [map_one, mul_one]

/-- 概要：無限根評価射は全ての根変数を指定根列へ送る。
方針：係数 1 の単項式の評価と指数モノイド射の変数公式を使う。
規約：全段 n の元の根の像を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の根付き入力射の照合。 -/
theorem powerRootPolynomialEval_variable (n : ℕ) :
    powerRootPolynomialEval p hp f ρ hρ (powerRootPolynomialVariable R p hp n) = ρ n := by
  change AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ) _
    (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul,
    powerRootExponentEvalHom_variable]

include hρ in
/-- 概要：係数と互換な根列を保つ無限根多項式環からの環射は一意に存在。
方針：具体的評価射を証人とし、係数・全根変数による外延性を使う。
規約：prism・分冪構造・完備性の仮定は不要。
使われ方：BS Rem 7.15（著者版 p.62）の指定 δ 射を根データで構成する準備。 -/
theorem existsUnique_powerRootPolynomialHom :
    ∃! F : P →+* B,
      F.comp (algebraMap R P) = f ∧
        ∀ n, F (powerRootPolynomialVariable R p hp n) = ρ n := by
  have hc : (powerRootPolynomialEval p hp f ρ hρ).comp (algebraMap R P) = f := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp f ρ hρ
  refine ⟨powerRootPolynomialEval p hp f ρ hρ,
    ⟨hc, powerRootPolynomialEval_variable p hp f ρ hρ⟩, ?_⟩
  intro F hF
  apply powerRootPolynomial_ringHom_ext p hp F _ (hF.1.trans hc.symm)
  intro n
  exact (hF.2 n).trans (powerRootPolynomialEval_variable p hp f ρ hρ n).symm

end SerrePositivity.BhattScholze.Andre
