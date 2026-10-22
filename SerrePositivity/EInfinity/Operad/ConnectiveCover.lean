module

public import SerrePositivity.EInfinity.Operad.AlgebraLimitCriterion
public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift

/-!
# 非正次数のオペラッド代数の smart connective cover

概要：各 arity が非正次数にあるオペラッドの代数に、元の τ≤0 と包含を構成する。
方針：元の作用を smart 切断へ一意に持ち上げ、単射な包含で全代数公理を反映する。
規約：任意の元の代数を扱い、零入力も含む。
使われ方：離散 E 代数の本質像の特徴付け。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Algebra
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A] {P : Operad A}

lemma power_nonpositive (X : Complex A) [X.IsStrictlyLE 0] (n : ℕ) :
    (TensorPowers.power X n).IsStrictlyLE 0 := by
  induction n with
  | zero => exact ConnectiveLift.unit_nonpositive
  | succ n ih =>
    let := ih
    exact ConnectiveLift.tensor_nonpositive X (TensorPowers.power X n)

variable (hP : ∀ n, (P.arity n).IsStrictlyLE 0) (B : P.Algebra)

def connectiveCoverAction (n : ℕ) :
    P.arity n ⊗ TensorPowers.power (B.carrier.truncLE 0) n ⟶ B.carrier.truncLE 0 := by
  let := hP n
  let := power_nonpositive (B.carrier.truncLE 0) n
  let := ConnectiveLift.tensor_nonpositive (P.arity n)
    (TensorPowers.power (B.carrier.truncLE 0) n)
  exact ConnectiveLift.lift
    ((P.arity n ◁ TensorPowers.map (B.carrier.ιTruncLE 0) n) ≫ B.action n)

lemma connectiveCoverAction_inclusion (n : ℕ) :
    connectiveCoverAction hP B n ≫ B.carrier.ιTruncLE 0 =
      (P.arity n ◁ TensorPowers.map (B.carrier.ιTruncLE 0) n) ≫ B.action n := by
  let := hP n
  let := power_nonpositive (B.carrier.truncLE 0) n
  let := ConnectiveLift.tensor_nonpositive (P.arity n)
    (TensorPowers.power (B.carrier.truncLE 0) n)
  exact ConnectiveLift.lift_inclusion _

def connectiveCover : P.Algebra :=
  ofJointlyMonicActions (B.carrier.truncLE 0) (fun _ : PUnit.{1} => B)
    (fun _ => B.carrier.ιTruncLE 0) (connectiveCoverAction hP B)
    (fun _ => connectiveCoverAction_inclusion hP B) (by
      intro T f g h
      have : Mono (B.carrier.ιTruncLE 0) := by
        change Mono (HomologicalComplex.ιTruncLE B.carrier (ComplexShape.embeddingUpIntLE 0))
        infer_instance
      exact (cancel_mono (B.carrier.ιTruncLE 0)).mp (h PUnit.unit))

def connectiveCoverInclusion : connectiveCover hP B ⟶ B where
  hom := B.carrier.ιTruncLE 0
  comm n := by
    change connectiveCoverAction hP B n ≫ B.carrier.ιTruncLE 0 = _
    rw [id_tensorHom]
    exact connectiveCoverAction_inclusion hP B n

end SerrePositivity.EInfinity.Operad.Algebra
