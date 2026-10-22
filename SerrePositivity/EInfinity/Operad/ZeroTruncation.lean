module

public import SerrePositivity.EInfinity.Operad.TensorPowerTruncationDesc
public import SerrePositivity.EInfinity.Operad.AlgebraColimitCriterion

/-!
# 非正次数のオペラッド代数の smart 零次商

概要：元の非正代数の τ≥0 に全 arity の作用を降ろし、元の商射を代数射にする。
方針：全入力の切断降下と係数付きテンソル冪の全射性で全公理を反映する。
規約：底の平坦性を仮定せず、零入力も含む。
使われ方：離散 E 代数との実擬同型の構成。
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

lemma powerMap_epi {X Y : Complex A} (f : X ⟶ Y) [Epi f] (n : ℕ) :
    Epi (TensorPowers.map f n) := by
  induction n with
  | zero => change Epi (𝟙 _); infer_instance
  | succ n ih =>
    have := ih
    exact TruncationDesc.tensor_epi f (TensorPowers.map f n)

variable (hP : ∀ n, (P.arity n).IsStrictlyLE 0) (B : P.Algebra) [B.carrier.IsStrictlyLE 0]

def zeroTruncationAction (n : ℕ) :
    P.arity n ⊗ TensorPowers.power (B.carrier.truncGE 0) n ⟶ B.carrier.truncGE 0 := by
  let := hP n
  exact descendCoefficientPower B.carrier (P.arity n) n (B.action n ≫ B.carrier.πTruncGE 0)

lemma zeroTruncationAction_projection (n : ℕ) :
    (P.arity n ◁ TensorPowers.map (B.carrier.πTruncGE 0) n) ≫ zeroTruncationAction hP B n =
      B.action n ≫ B.carrier.πTruncGE 0 := by
  let := hP n
  exact projection_descendCoefficientPower _ _ _ _

def zeroTruncation : P.Algebra :=
  ofJointlyEpicActions (B.carrier.truncGE 0) (fun _ : PUnit.{1} => B)
    (fun _ => B.carrier.πTruncGE 0) (zeroTruncationAction hP B)
    (fun _ => zeroTruncationAction_projection hP B) (by
      intro Q n T f g h
      have := powerMap_epi (B.carrier.πTruncGE 0) n
      have ht := TruncationDesc.tensor_epi (𝟙 Q) (TensorPowers.map (B.carrier.πTruncGE 0) n)
      rw [id_tensorHom] at ht
      exact (cancel_epi (Q ◁ TensorPowers.map (B.carrier.πTruncGE 0) n)).mp (h PUnit.unit))

def zeroTruncationProjection : B ⟶ zeroTruncation hP B where
  hom := B.carrier.πTruncGE 0
  comm n := by
    rw [id_tensorHom]
    exact (zeroTruncationAction_projection hP B n).symm

lemma zeroTruncationProjection_quasiIso [B.carrier.IsGE 0] :
    QuasiIso (zeroTruncationProjection hP B).hom := by
  change QuasiIso (B.carrier.πTruncGE 0)
  exact (CochainComplex.quasiIso_πTruncGE_iff B.carrier 0).mpr inferInstance

lemma zeroTruncation_nonpositive : (zeroTruncation hP B).carrier.IsStrictlyLE 0 :=
  TruncationDesc.truncation_nonpositive B.carrier 0

lemma zeroTruncation_nonnegative : (zeroTruncation hP B).carrier.IsStrictlyGE 0 := by
  change (B.carrier.truncGE 0).IsStrictlyGE 0
  infer_instance

end SerrePositivity.EInfinity.Operad.Algebra
