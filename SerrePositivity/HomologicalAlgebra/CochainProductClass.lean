module

public import SerrePositivity.HomologicalAlgebra.CochainProduct
import all SerrePositivity.HomologicalAlgebra.CochainProduct
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# 余鎖積のコホモロジー類による計算

## 概要
余輪体の積の類は、それぞれのコホモロジー類の積になる。

## 方針
抽象的な余輪体を微分の核と同一視し、核の商で積を計算する。

## 規約
余輪体の条件は隣の次数への微分で書く。

## 使われ方
de Rham と Čech の積の比較。
-/

public noncomputable section

open CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.HomologicalAlgebra.CochainProduct

variable {R : Type u} [CommRing R] {K : CochainComplex (ModuleCat.{u} R) ℕ}

/-- 閉余鎖のコホモロジー類。 -/
def closedClass (n : ℕ) (x : K.X n) (h : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n (K.cyclesMk x (n + 1) (CochainComplex.next ℕ n) h)

private theorem class_eq_mk {n : ℕ} (z : Z (K := K) n) :
    closedClass n z.1 (cycle_d z) =
      (K.sc n).moduleCatHomologyIso.inv (Submodule.Quotient.mk z) := by
  let S := K.sc n
  let c := K.cyclesMk z.1 (n + 1) (CochainComplex.next ℕ n) (cycle_d z)
  have hc : c = S.moduleCatCyclesIso.inv z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    change K.iCycles n c = S.iCycles (S.moduleCatCyclesIso.inv z)
    have hc : K.iCycles n c = z.1 := K.i_cyclesMk z.1 (n + 1) (CochainComplex.next ℕ n) _
    have hh := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles z
    change S.iCycles (S.moduleCatCyclesIso.inv z) = z.1 at hh
    exact hc.trans hh.symm
  change S.homologyπ c = _
  rw [hc]
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π z

/-- 余輪体の積はコホモロジーの積を代表する。 -/
theorem onHomology_closedClass (M : CochainProduct K) {i j : ℕ}
    (x : K.X i) (y : K.X j) (hx : K.d i (i + 1) x = 0) (hy : K.d j (j + 1) y = 0)
    (hxy : K.d (i + j) (i + j + 1) (M.mul i j x y) = 0) :
    M.onHomology (closedClass i x hx) (closedClass j y hy) =
      closedClass (i + j) (M.mul i j x y) hxy := by
  let a : Z (K := K) i := ⟨x, by
    change K.d i ((ComplexShape.up ℕ).next i) x = 0
    rwa [CochainComplex.next]⟩
  let b : Z (K := K) j := ⟨y, by
    change K.d j ((ComplexShape.up ℕ).next j) y = 0
    rwa [CochainComplex.next]⟩
  change M.onHomology (closedClass i a.1 (cycle_d a)) (closedClass j b.1 (cycle_d b)) =
    closedClass (i + j) (M.cycleMul a b).1 (cycle_d (M.cycleMul a b))
  rw [class_eq_mk, class_eq_mk, class_eq_mk]
  unfold onHomology
  rw [show (K.sc i).moduleCatHomologyIso.hom
      ((K.sc i).moduleCatHomologyIso.inv (Submodule.Quotient.mk a)) = Submodule.Quotient.mk a
      from ConcreteCategory.congr_hom (K.sc i).moduleCatHomologyIso.inv_hom_id _,
    show (K.sc j).moduleCatHomologyIso.hom
      ((K.sc j).moduleCatHomologyIso.inv (Submodule.Quotient.mk b)) = Submodule.Quotient.mk b
      from ConcreteCategory.congr_hom (K.sc j).moduleCatHomologyIso.inv_hom_id _]
  rfl

end SerrePositivity.HomologicalAlgebra.CochainProduct
