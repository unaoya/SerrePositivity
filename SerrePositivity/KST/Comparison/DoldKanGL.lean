module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# ĜL の入力となる単元成分の逆像

概要：KST §2.2、式 (2.2) の代数的な逆像を定義し、群とは限らないことを検証する。
方針：ℤ[X] の 1+X を零点と −1 で評価する。原典の群状単体的モノイドという区別を保つ。
規約：SS03 Proposition 2.13 の Γ と式 (2.9) の AW 積はまだ実装していない。
使われ方：L2a の「単体的群」という要求の設計変更を検討するための代数的反例。
-/

public section

namespace SerrePositivity.KST.Comparison

universe u v

/--
概要：環準同型による単元の逆像を部分モノイドにする。
方針：単元の積に関する閉性を用いる。
規約：逆像の各元が元の環で可逆であるとは要求しない。
使われ方：KST §2.2、式 (2.2) の各単体次数での代数的構成。
-/
def unitsPreimage {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) : Submonoid R where
  carrier := {x | IsUnit (f x)}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change IsUnit (f (x * y))
    rw [map_mul]
    exact hx.mul hy

/--
概要：零点評価で整数の単元になる多項式の部分モノイド。
方針：`unitsPreimage` に評価準同型を適用する。
規約：これは単体的環そのものの構成ではなく、零次で現れる代数的模型である。
使われ方：KST 式 (2.2) と SS03 式 (2.9) の群とモノイドの区別を検証する。
-/
noncomputable def evalZeroUnits : Submonoid (Polynomial ℤ) :=
  unitsPreimage (Polynomial.evalRingHom (0 : ℤ))

/--
概要：1+X は零点評価による単元の逆像に属する。
方針：評価すると 1 になることを使う。
規約：多項式環での単元性は結論に含まない。
使われ方：KST 式 (2.2) の逆像が単元群と異なることの検証。
-/
theorem one_add_X_mem_evalZeroUnits :
    (1 + Polynomial.X : Polynomial ℤ) ∈ evalZeroUnits := by
  change IsUnit (Polynomial.evalRingHom (0 : ℤ) (1 + Polynomial.X))
  simp

/--
概要：整数係数多項式 1+X は単元ではない。
方針：右逆元との積を −1 で評価すると 0 = 1 となる。
規約：この評価による証明は原典にはない代数的な反例検証である。
使われ方：KST 式 (2.2) の逆像に群構造を要求できないことを示す。
-/
theorem not_isUnit_one_add_X : ¬ IsUnit (1 + Polynomial.X : Polynomial ℤ) := by
  intro h
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have h := congrArg (Polynomial.evalRingHom (-1 : ℤ)) hq
  simp at h

/--
概要：単元の逆像部分モノイドに属する 1+X は、その中に右逆元を持たない。
方針：部分モノイドの等式を多項式環に写し、−1 で評価する。
規約：部分モノイドの乗法を固定した主張であり、任意の別の群構造は扱わない。
使われ方：KST §2.2 の群状モノイドを単体的群と呼べないことの代数的根拠。
-/
theorem one_add_X_no_right_inverse :
    ¬ ∃ q : evalZeroUnits,
      (⟨1 + Polynomial.X, one_add_X_mem_evalZeroUnits⟩ : evalZeroUnits) * q = 1 := by
  rintro ⟨q, hq⟩
  have hp : (1 + Polynomial.X : Polynomial ℤ) * q.val = 1 :=
    congrArg (fun r : evalZeroUnits => r.val) hq
  have h := congrArg (Polynomial.evalRingHom (-1 : ℤ)) hp
  simp at h

end SerrePositivity.KST.Comparison
