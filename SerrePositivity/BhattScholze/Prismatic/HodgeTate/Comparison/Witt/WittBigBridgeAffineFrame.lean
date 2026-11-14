module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridge
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison

/-!
# 結晶の橋の有限 prismatic 枠での座標

## 概要
大きい枠の結晶の橋を有限 affine 枠に制限したときの、係数と変数の像を求める。

## 方針
有限枠から大きい枠への標準射と、各項の結晶の橋の標準脚で検査する。

## 規約
係数は ψ、各頂点の変数は対応する Witt 枠の変数の p 乗。

## 使われ方
BS 著者版 Theorem 6.4 の ψ に沿う導来 p 完備底変換で、有限枠上の比較を同定する。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittBigBridge

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable {Q : Poly (A ⧸ P.ideal)} {n : ℕ} {κ : Cardinal.{u}}
variable (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n)

/-- 結晶の橋を有限 affine 枠に制限した環射。 -/
def fromAffineFrame : X.X.B →+* (WittBigCrystalline.term P hpC hlocal Q n).carrier :=
  (bridgeAt P hpA hpC hlocal Q n Y).comp (affineToBig X Y)

/-- 有限枠からの結晶の橋は基底上で ψ に一致する。 -/
theorem fromAffineFrame_base :
    (fromAffineFrame P hpA hpC hlocal X Y).comp X.X.toHom.toRingHom =
      (algebraMap (WittVector p (A ⧸ P.ideal))
        (WittBigCrystalline.term P hpC hlocal Q n).carrier).comp (psiRing P hpA) := by
  unfold fromAffineFrame
  rw [RingHom.comp_assoc, (affineToBig_spec X Y).2.1,
    (bridgeAt_spec P hpA hpC hlocal Q n Y).2.1] <;> rfl

/-- 有限枠の各頂点の変数の像は、Witt 枠の対応する変数の p 乗。 -/
theorem fromAffineFrame_variable (j : Fin Q.n) (i : Fin (n + 1)) :
    fromAffineFrame P hpA hpC hlocal X Y (X.η (affineVariable P Q.n n j i)) =
      (WittBigCrystalline.term P hpC hlocal Q n).unit
        (MvPolynomial.X (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j), i)) ^ p := by
  change bridgeAt P hpA hpC hlocal Q n Y (affineToBig X Y (X.η (affineVariable P Q.n n j i))) =
    (termAt P hpC hlocal Q n).unit
      (MvPolynomial.X (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j), i)) ^ p
  rw [(affineToBig_spec X Y).2.2, (bridgeAt_spec P hpA hpC hlocal Q n Y).2.2]
  rfl

end SerrePositivity.BhattScholze.Prismatic.WittBigBridge
