module
public import SerrePositivity.KST.ProExcision.OneDifferenceTransform

/-!
# 三角部分環に作用する左乗法

概要：部分環の元を右から固定する周囲の元の左乗法は非単位環準同型になる。
方針：積では中央の xB=x を使い、加法と所属は直接確認する。
規約：KST Lemma 4.16 の first n 行への左行列作用。
使われ方：ブロック対角行列の作用を実三角群の自己準同型に持ち上げる。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：右から全ての部分環の元を固定する乗数の左乗法は非単位環準同型。
方針：結合律と xB=x から B(xy)=(Bx)(By) を導く。
規約：KST 4.16、全環上の環準同型とはしない。
使われ方：行列 M の first n 行への作用の非単位三角部分での構成。 -/
def leftMultiplierHom (S : NonUnitalSubring R) (B : R)
    (hpreserve : ∀ x, x ∈ S → B * x ∈ S) (hright : ∀ x, x ∈ S → x * B = x) : S →ₙ+* S where
  toFun x := ⟨B * (x : R), hpreserve x x.property⟩
  map_zero' := by apply Subtype.ext; exact mul_zero B
  map_add' x y := by apply Subtype.ext; exact mul_add B (x : R) (y : R)
  map_mul' x y := by
    apply Subtype.ext
    change B * ((x : R) * (y : R)) = (B * (x : R)) * (B * (y : R))
    calc
      _ = B * (((x : R) * B) * (y : R)) := by rw [hright x x.property]
      _ = _ := by simp only [mul_assoc]

/-- 概要：左乗数による非単位部分環の作用は実単位部分群の自己準同型を与える。
方針：非単位環準同型を 1 からの差の群へ持ち上げる。
規約：KST Lemma 4.16 の行列作用の基礎、可逆な B を仮定しない。
使われ方：一般の行列のモノイド作用を単位群上に定義する。 -/
def leftMultiplierGroupHom (S : NonUnitalSubring R) (B : R)
    (hpreserve : ∀ x, x ∈ S → B * x ∈ S) (hright : ∀ x, x ∈ S → x * B = x) :
    oneDifferenceSubgroup S →* oneDifferenceSubgroup S :=
  oneDifferenceTransform S S (leftMultiplierHom S B hpreserve hright)

end SerrePositivity.KST.ProExcision
