module
public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 境界cellの可換squareと逐次列の準同型判定の監査

## 概要
境界cellの可換squareと逐次列の準同型判定の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (S : Type v) (D : Type w)
  [DGCategory A S] [DGCategory A D] [Small.{u} S]

-- targetの対象集合のsmallnessはcell添字に不要。
example (F : DGFunctor A S D) : Small.{u} (DGCategoryBoundaryCells.Index A S D F) :=
  inferInstance

example (F : DGFunctor A S D) (x y : S) (c : ComplexBoundaryCell A (F.map x y)) :
    c.attachingMap A ≫ F.map x y = complexSphereToDisk A c.degree ≫ c.targetDiskMap A :=
  c.augmentation_square A

example (F : DGFunctor A S D) (x y : S)
    (h : ∀ c : ComplexBoundaryCell A (F.map x y), c.HasFilling A) :
    QuasiIso (F.map x y) := ComplexBoundaryCell.quasiIso_of_filling A h

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D] :
    Small.{0} (DGCategoryBoundaryCells.Index (ZMod 2)
      (DGCategoryCycleCover.Source (ZMod 2) D) D (DGCategoryCycleCover.augmentation (ZMod 2) D)) :=
  inferInstance

#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.attachingMap
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.targetDiskMap
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.targetDiskMap_generator
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.augmentation_square
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.HasFilling
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.quasiIso_of_filling
#print axioms SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells.Index
#print axioms SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells.indexSmall
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.sequential_filling
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.sequential_quasiIso
