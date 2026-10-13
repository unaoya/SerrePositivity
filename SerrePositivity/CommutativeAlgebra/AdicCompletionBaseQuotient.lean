module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionQuotient
public import Mathlib.RingTheory.Ideal.Over

/-! # 基底の冪商上での完備化の商同型

基底環Bの有限生成イデアルIをB代数Sへ拡張し、その完備化Cを取る。
C/I^n CとS/I^n Sの同型を、B/I^n上の代数同型として構成する。
局所性・Noether性・平坦性は仮定しない。零乗も含む。
-/

@[expose] public section
namespace SerrePositivity
variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
variable (I : Ideal B) (hI : I.FG)

/-- 完備化の冪商を、基底の冪商上で元の環の冪商に同定する。 -/
noncomputable def adicCompletionBasePowQuotientEquiv (n : ℕ) :
    let J := I.map (algebraMap B S)
    let C := AdicCompletion J S
    (C ⧸ ((I ^ n).map (algebraMap B C))) ≃ₐ[B ⧸ (I ^ n)]
      (S ⧸ ((I ^ n).map (algebraMap B S))) := by
  let J := I.map (algebraMap B S)
  let C := AdicCompletion J S
  have hC : (J.map (algebraMap S C)) ^ n = (I ^ n).map (algebraMap B C) := by
    rw [Ideal.map_pow]
    have hmap : J.map (algebraMap S C) = I.map (algebraMap B C) := by
      change (I.map (algebraMap B S)).map (algebraMap S C) = _
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B S C]
    rw [hmap]
  have hS : J ^ n = (I ^ n).map (algebraMap B S) := by
    rw [Ideal.map_pow]
  let e : (C ⧸ ((I ^ n).map (algebraMap B C))) ≃ₐ[S]
      (S ⧸ ((I ^ n).map (algebraMap B S))) :=
    ((Ideal.quotientEquivAlgOfEq S hC.symm).trans
      (adicCompletionPowQuotientEquiv J (hI.map _) n)).trans
      (Ideal.quotientEquivAlgOfEq S hS)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e (Ideal.Quotient.mk _ (algebraMap B C b)) =
    Ideal.Quotient.mk _ (algebraMap B S b)
  rw [IsScalarTower.algebraMap_apply B S C]
  exact e.commutes (algebraMap B S b)

end SerrePositivity
