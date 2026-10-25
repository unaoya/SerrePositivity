module

public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPQuotientFlat

/-!
# André E1：分冪表示環の実 p 乗商上の自由性

## 概要

標数 p の任意の環 B と元 y について、具体的な分冪表示環は B/(y^p) 上自由である。
BS 著者版 Rem 7.15(1)（p.62）の自由性の計算を既存の一元分冪基底から得る。

## 方針

切断多項式環上の自由基底の基底変更を、実 y 評価商と整合する係数射に沿って移す。
最後に分冪表示環と評価テンソルの代数同型で自由性を戻す。

## 規約

対象は `PrincipalDPPresentation` であり、実 prismatic envelope との同型は含まない。
本結果は y の非零因子性を必要としない。原典の prismatic cover の証明とは別の通常代数計算。

## 使われ方

モニック f の商 B/(f^p) の自由性と合成し、元の係数環上の分冪表示環の自由性を得る。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra

/-- 概要：評価した分冪添加環は元 y の実 p 乗商上自由。
方針：評価商の同定を経由して、既存の切断多項式上の基底を移す。
規約：係数射は `rankOneDPEvaluatedQuotientAlgebra` の指定射に固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪表示環の自由性。 -/
theorem evaluatedDP_quotient_free
    {B : Type u} [CommRing B] (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := rankOneDPEvaluatedQuotientAlgebra (A := B) hprime.pos hp y
    Module.Free (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope B B y) := by
  let : Algebra (Polynomial B) B := rankOneDPEvaluationAlgebra (A := B) y
  let Q := B ⧸ Ideal.span {y ^ p}
  let Q' := B ⧸ Ideal.span {(algebraMap (Polynomial B) B Polynomial.X) ^ p}
  let T := RankOneDPEvaluatedEnvelope B B y
  let eQ : Q ≃+* Q' := Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := B) p y)
  let : Algebra Q Q' := eQ.toRingHom.toAlgebra
  let : Algebra Q' T := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Algebra Q T := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower Q Q' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : Q ≃ₐ[Q] Q' := { __ := eQ, commutes' := fun _ => rfl }
  let : Module.Free Q Q' :=
    Module.Free.of_basis ((Module.Basis.singleton Unit Q).map e.toLinearEquiv)
  let : Module.Free Q' T := rankOneDPQuotientToEnvelope_moduleFree hprime hp
  exact Module.Free.trans (R := Q) (S := Q') (M := T)

/-- 概要：具体的分冪表示環は元の実 p 乗商上自由。
方針：実商上の代数同型で評価した分冪添加環の自由性を戻す。
規約：零環と零因子 y を許す。実 pd 包との同定は別工程。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック関係の自由性。 -/
theorem principalDPPresentation_quotient_free
    {B : Type u} [CommRing B] (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hprime.pos hp y
    Module.Free (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotientAlgebra (A := B) hprime.pos hp y
  let := evaluatedDP_quotient_free p hprime hp y
  exact Module.Free.of_equiv (principalDPQuotientTensorAlgEquiv hprime.pos hp y).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre
