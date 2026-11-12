module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# 成分の符号を変えない余鎖の始域のシフト

## 概要
元のシフトの次数同型の後に同じ成分を合成する、始域のシフトを記録する。

## 方針
既存 leftShift の定数符号を同じ符号で打ち消し、微分との整合を計算する。

## 規約
既存のシフト・leftShift の定義は変更しない。

## 使われ方
HA 1.2.4。coherent bar の shifted 因子と全複体の元の直和包含の照合。
-/

@[expose] public noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ} {n : ℤ}

/-- 同じ次数同型と元の成分だけで与える、始域のシフト。 -/
def unsignedLeftShift (z : Cochain K L n) (a n' : ℤ) (h : n + a = n') :
    Cochain (K⟦a⟧) L n' :=
  (a * n' + a * (a - 1) / 2).negOnePow • z.leftShift a n' h

/-- 各成分は、シフトの元の次数同型の後の同じ成分。 -/
theorem unsignedLeftShift_v (z : Cochain K L n) (a n' : ℤ) (h : n + a = n')
    (p q : ℤ) (hpq : p + n' = q) :
    (unsignedLeftShift z a n' h).v p q hpq =
      (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ z.v (p + a) q (by omega) := by
  simp only [unsignedLeftShift, Cochain.units_smul_v, z.leftShift_v a n' h p q hpq
    (p + a) (by omega), smul_smul, Int.units_mul_self, one_smul]

/-- 成分を変えない始域のシフトは、同じ cochain 微分に両立する。 -/
theorem unsignedLeftShift_δ (z : Cochain K L n) (a n' : ℤ) (h : n + a = n')
    (m m' : ℤ) (hm : m + a = m') :
    δ n' m' (unsignedLeftShift z a n' h) = unsignedLeftShift (δ n m z) a m' hm := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    unfold unsignedLeftShift
    rw [δ_units_smul, z.δ_leftShift a n' m' h m hm, smul_smul, ← Int.negOnePow_add]
    have he : (a * n' + a * (a - 1) / 2) + a = a * m' + a * (a - 1) / 2 := by
      rw [← hnm']
      ring
    rw [he]
  · have hnm' : ¬ n' + 1 = m' := by omega
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm]
    simp [unsignedLeftShift]

end SerrePositivity.HomologicalAlgebra
