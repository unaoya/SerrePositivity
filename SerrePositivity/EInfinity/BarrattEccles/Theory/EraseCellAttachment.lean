module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AttachCoproductCells
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAlgebraAdjunction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDisk
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# セル付加の次数付き自由表示の後続段

## 概要
Berger–Moerdijk 命題 4.1 のセル付加で、微分を消した後の台を計算する。

## 方針
付加の pushout を随伴で保存し、各 disk の境界を余積の一方の因子として消去する。

## 規約
指定された付加の包含射と、自由代数の比較の自然性を用いる。

## 使われ方
始対象から始めるセル代数の次数付き自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory Limits HomotopicalAlgebra DifferentialGraded

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

variable {X Y : P.Algebra} {f : X ⟶ Y}
  (c : AttachCells.{u} (fun n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The erased attachment, expressed using the erased free generators. -/
def eraseAttachment :
    AttachCells.{u}
      (fun n => P.erase.freeAlgebraFunctor.map
        ((eraseDifferential A).map (complexSphereToDisk A n))) (P.eraseAlgebra.map f) := by
  let a := mapAttachCells c P.eraseAlgebra
  let e := P.eraseFreeAlgebraIso
  exact a.reindexCellTypes _ id (fun n =>
    Arrow.isoMk (e.app (complexSphere A (n + 1))) (e.app (complexDisk A n))
      (e.hom.naturality (complexSphereToDisk A n)).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseAttachment)

/-- The erased attachment freely adjoins the spheres of the new cells. -/
def eraseAttachmentCofanIsColimit :
    let a := P.eraseAttachment c
    IsColimit (attachComplementCofan a
      (fun n => P.erase.freeAlgebraFunctor.map (erasedDiskSphereSplitting A n).s)) := by
  dsimp only
  letI := P.erase.freeAlgebraAdjunction.isLeftAdjoint
  apply attachComplementIsColimit
  intro n
  exact mapIsColimitOfPreservesOfIsColimit P.erase.freeAlgebraFunctor _ _
    (erasedDiskCofanIsColimit A n)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseAttachmentCofanIsColimit)

end SerrePositivity.EInfinity.Operad
