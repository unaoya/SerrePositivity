module
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Algebra.Hom

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 基底の下の代数の台加群と単体の添字

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic
namespace PDCechNerve

/-- 基底の下の可換環の台加群。 -/
@[expose] def algebraModule (k : Type u) [CommRing k] :
    Under (CommRingCat.of k) ⥤ ModuleCat.{u} k :=
  (commAlgCatEquivUnder (CommRingCat.of k)).inverse ⋙
    forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙ forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)

private theorem val_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).val = if j.val < i.val then j.val else j.val + 1 := by
  by_cases h : j.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt i j h, ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

private theorem val_predAbove {n : ℕ} (i : Fin n) (j : Fin (n + 1)) :
    (i.predAbove j).val = if i.val < j.val then j.val - 1 else j.val := by
  by_cases h : i.val < j.val
  · rw [Fin.predAbove_of_castSucc_lt i j h, ite_eq_left h]
    rfl
  · rw [Fin.predAbove_of_le_castSucc i j (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

end PDCechNerve

end SerrePositivity.BhattScholze.Prismatic
