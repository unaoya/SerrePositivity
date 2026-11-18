module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerTruncationDesc
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraColimitCriterion

/-!
模型。文献の定義との比較は後で
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
namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

lemma powerMap_epi {X Y : Complex A} (f : X ⟶ Y) [Epi f] (n : ℕ) :
    Epi (_root_.SerrePositivity.TensorPowers.map f n) := by
  induction n with
  | zero => change Epi (𝟙 _); infer_instance
  | succ n ih =>
    have := ih
    exact TruncationDesc.tensor_epi f (_root_.SerrePositivity.TensorPowers.map f n)

variable (hP : ∀ n, (P.arity n).IsStrictlyLE 0) (B : P.Algebra) [B.carrier.IsStrictlyLE 0]

def zeroTruncationAction (n : ℕ) :
    P.arity n ⊗ _root_.SerrePositivity.TensorPowers.power (B.carrier.truncGE 0) n ⟶ B.carrier.truncGE 0 := by
  let := hP n
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.descendCoefficientPower B.carrier (P.arity n) n (B.action n ≫ B.carrier.πTruncGE 0)

lemma zeroTruncationAction_projection (n : ℕ) :
    (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (B.carrier.πTruncGE 0) n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncationAction hP B n =
      B.action n ≫ B.carrier.πTruncGE 0 := by
  let := hP n
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.projection_descendCoefficientPower _ _ _ _

def zeroTruncation : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofJointlyEpicActions (B.carrier.truncGE 0) (fun _ : PUnit.{1} => B)
    (fun _ => B.carrier.πTruncGE 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncationAction hP B)
    (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncationAction_projection hP B) (by
      intro Q n T f g h
      have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.powerMap_epi (B.carrier.πTruncGE 0) n
      have ht := TruncationDesc.tensor_epi (𝟙 Q) (_root_.SerrePositivity.TensorPowers.map (B.carrier.πTruncGE 0) n)
      rw [id_tensorHom] at ht
      exact (cancel_epi (Q ◁ _root_.SerrePositivity.TensorPowers.map (B.carrier.πTruncGE 0) n)).mp (h PUnit.unit))

def zeroTruncationProjection : B ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncation hP B where
  hom := B.carrier.πTruncGE 0
  comm n := by
    rw [id_tensorHom]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncationAction_projection hP B n).symm

lemma zeroTruncationProjection_quasiIso [B.carrier.IsGE 0] :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncationProjection hP B).hom := by
  change QuasiIso (B.carrier.πTruncGE 0)
  exact (CochainComplex.quasiIso_πTruncGE_iff B.carrier 0).mpr inferInstance

lemma zeroTruncation_nonpositive : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncation hP B).carrier.IsStrictlyLE 0 :=
  TruncationDesc.truncation_nonpositive B.carrier 0

lemma zeroTruncation_nonnegative : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.zeroTruncation hP B).carrier.IsStrictlyGE 0 := by
  change (B.carrier.truncGE 0).IsStrictlyGE 0
  infer_instance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
