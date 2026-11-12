module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarFaceDifferential
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarCoefficients
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.NerveInclusion

/-!
# 小さい strict bar の同じ一次 shift ブロックの係数

## 概要
先頭を保つ面の係数を恒等射、最初の prefix の係数を元の先頭の射と照合する。

## 方針
既存の端点輸送の異種等号と、strict nerve の次数零の成分を使う。

## 規約
既存の shift ブロックとその端点輸送を保つ。

## 使われ方
HA 1.2.4。全単体境界と既存 theta の一次列の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SerrePositivity.DifferentialGraded SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 元の先頭を保つ面は、同じ先頭の係数の単位 shift ブロックである。 -/
theorem smallStrictBarFaceBlock_heq (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (dgCoherentBarFaceBlock A PUnit.{1} (smallStrictBarDiagram A F) s i)
      (moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ)
        (M := ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))
        (N := ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))
        (unitElement A (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))).val
        (show ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1 by omega)) :=
  dgCoherentBarFaceBlock_heq A PUnit.{1} (smallStrictBarDiagram A F) s i

/-- 最初の prefix の同じ係数は、元の strict 図式の先頭の射。 -/
theorem smallStrictBarPrefixHom_zero (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    HEq (dgCoherentBarPrefixHom A PUnit.{1} (smallStrictBarDiagram A F) s 0 (by omega))
      ((closedHomEquiv A (RightModule A PUnit.{1}) (F.obj (s.down.obj 0)) (F.obj (s.down.obj (Fin.succ 0)))
        (F.map (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1)))))))).val) := by
  unfold dgCoherentBarPrefixHom
  apply (gradedHomTransport_heq _ _ _ _).trans
  apply heq_of_eq
  rw [coherentDiagramTop]
  exact closedNerveHom_zero _

/-- 先頭を保つ面の shifted 因子は、同じ先頭の値の n シフト。 -/
theorem smallStrictBarFaceFamily (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) (i : Fin (n + 1)) :
    dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) (dgCoherentBarFace s i.succ) =
      ForgetEnrichment.of (Complex A) (shiftModule (n : ℤ)
        (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj 0)))) := rfl

/-- 最初の tail の shifted 因子は、元の二つ目の値の n シフト。 -/
theorem smallStrictBarTailFamily (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarTail s 1 (by omega)) =
      ForgetEnrichment.of (Complex A) (shiftModule (n : ℤ)
        (ForgetEnrichment.to (Complex A) (F.obj (s.down.obj (Fin.succ 0))))) := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
