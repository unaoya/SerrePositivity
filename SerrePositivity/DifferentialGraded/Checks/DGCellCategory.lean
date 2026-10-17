module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Category
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cell付加の豊穣dg圏・包含関手・符号の監査

## 概要
任意次数cell付加の豊穣dg圏・包含関手・符号の監査。

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
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

-- 対象宇宙とcell添字宇宙は独立。Homのflatnessは不要。
example : DGCategory A (C.Objects A D I) := inferInstance

example : DGFunctor A D (C.Objects A D I) := C.embedding A D I

example : D ≃ C.Objects A D I := C.objectEquiv A D I

example [Small.{u} D] : Small.{u} (C.Objects A D I) := inferInstance

example (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (f : (C.attachedHom A D I x y).X p) (g : (C.attachedHom A D I y z).X q) :
    (C.attachedComposition A D I x y z).f n
      (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • compose A (x := (⟨x⟩ : C.Objects A D I))
      (y := (⟨y⟩ : C.Objects A D I)) (z := (⟨z⟩ : C.Objects A D I)) g f hn :=
  C.attachedComposition_eq_signed_compose A D I x y z p q n hn f g

example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) : DGFunctor (ZMod 2) D (C.Objects (ZMod 2) D I) :=
  C.embedding (ZMod 2) D I

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_f
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_original
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_apply
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedIdentity
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedIdentity_f
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_left_unit
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_right_unit
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_assoc
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.Objects
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.objectEquiv
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.objectsSmall
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedDGCategory
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.embedding
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedComposition_eq_signed_compose
