module

public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimePresentation
public import SerrePositivity.BhattScholze.PrincipalDPQuotientFlat

/-!
# André E1・E2：可算切断表示の普遍射と素数冪生成元の外延性

## 概要

可算切断商からの射を p 乗が零となる元族から構成し、
一元分冪代数と一次関係商からの射を素数冪分冪の値で比較する。
BS Rem 7.15(1)（著者版 p.62）の γ₁=f の商を計算する準備。

## 方針

多項式評価を商に降ろし、既に構成した可算切断表示の全射性を使う。

## 規約

普遍射自体は任意の自然数 p に対して定義する。分冪側の外延性には
p が素数で係数環内で零であることを使う。

## 使われ方

一次関係商と係数 p 乗商上の切断多項式商の間に互いに逆な射を構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ)
variable {B : Type u} [CommRing B] [Algebra A B]

/-- 概要：p 乗が零となる元族への指定値から可算切断商の係数代数射を作る。
方針：多項式評価が全ての p 乗関係を消すことを使う。
規約：素数性や標数は前提にしない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断商の普遍性。 -/
def dividedPowerPrimeTruncatedLift (b : ℕ → B) (hb : ∀ i, b i ^ p = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] B := by
  let g : MvPolynomial ℕ A →ₐ[A] B := MvPolynomial.aeval b
  apply Ideal.Quotient.liftₐ _ g
  have hker : monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, hb]
  exact fun _ hx => hker hx

/-- 概要：可算切断商の普遍射は変数を指定した元へ送る。
方針：商と多項式評価の公式を使う。
規約：変数番号を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の二つの表示の比較。 -/
theorem dividedPowerPrimeTruncatedLift_X (b : ℕ → B) (hb : ∀ i, b i ^ p = 0) (i : ℕ) :
    dividedPowerPrimeTruncatedLift (A := A) p b hb
      (Ideal.Quotient.mk _ (MvPolynomial.X i)) = b i := by
  simp [dividedPowerPrimeTruncatedLift]

/-- 概要：一元分冪代数からの射は全素数冪分冪上の値で一意に決まる。
方針：可算切断評価の全射性と、切断変数上の外延性を使う。
規約：p は素数で係数環内で零。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係商の射の照合。 -/
theorem dividedPowerPrimeHom_ext [Fact p.Prime] (hp : (p : A) = 0)
    (f g : DividedPowerAlgebra A A →ₐ[A] B)
    (h : ∀ i, f (DividedPowerAlgebra.dp A (p ^ i) (1 : A)) =
      g (DividedPowerAlgebra.dp A (p ^ i) (1 : A))) : f = g := by
  have hc : f.comp (dividedPowerPrimeTruncatedEval p hp) =
      g.comp (dividedPowerPrimeTruncatedEval p hp) := by
    apply dividedPowerPrimeTruncatedHom_ext
    intro i
    simpa only [AlgHom.comp_apply, dividedPowerPrimeTruncatedEval_X] using h i
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := dividedPowerPrimeTruncatedEval_surjective p hp x
  exact DFunLike.congr_fun hc y

/-- 概要：一次関係商からの射は全素数冪分冪の標準像上の値で一意に決まる。
方針：商の射を自由分冪代数へ引き戻し、素数冪生成元で比較する。
規約：入力 y の正則性はこの外延性には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の逆合成の確認。 -/
theorem principalDPPrimeHom_ext [Fact p.Prime] (hp : (p : A) = 0) (y : A)
    (f g : PrincipalDPPresentation A y →ₐ[A] B)
    (h : ∀ i, f (principalDPGenerator y (p ^ i)) =
      g (principalDPGenerator y (p ^ i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply dividedPowerPrimeHom_ext p hp
  exact h

end SerrePositivity.BhattScholze.Andre
