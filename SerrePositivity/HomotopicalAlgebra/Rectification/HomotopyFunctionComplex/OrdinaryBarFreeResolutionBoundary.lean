module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual next free-resolution boundary from the preceding face equations。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0179][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0179
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual next free-resolution boundary from the preceding face equations

The source faces are the fixed-object reversed faces of the existing comonad
resolution. Their relations imply every boundary overlap; these overlaps are
proved here, not additional data in the construction.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary
open OrdinaryBarFreeDiagramExtension FreeGeneratorCategories FreeGeneratorDegeneracies
open FreeGeneratorFaces OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      fixedFace D (n + 1) i ⋙ G)

def face (k : Fin (n + 3)) :
    degree D (n + 3) ⥤ target (C := C) hcof hfib (parameters P (n + 1)) :=
  fixedFace D (n + 2) k ⋙ F

include faceLaw in
lemma face_overlap (j k : Fin (n + 3)) (hjk : j < k) :
    face hcof hfib D n P F j ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk))) =
    face hcof hfib D n P F k ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk))) := by
  rw [face, face, CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    faceLaw, faceLaw, ← CategoryTheory.Functor.assoc, ← CategoryTheory.Functor.assoc,
    fixedFace_overlap D (n + 1) j k hjk]

def seed : degree D (n + 2) ⥤q target (C := C) hcof hfib (parameters P (n + 1)) :=
  Paths.of (degree D (n + 2)) ⋙q (face hcof hfib D n P F 0).toPrefunctor

def faceValues (k : Fin (n + 3)) {X Y : degree D (n + 2)} (e : X ⟶ Y) :
    (seed hcof hfib D n P F).obj X ⟶ (seed hcof hfib D n P F).obj Y :=
  (face hcof hfib D n P F k).map e.toPath

include faceLaw in
lemma values_compatible {X Y : degree D (n + 2)} (e : X ⟶ Y) :
    Compatible hcof hfib n (fun k => faceValues hcof hfib D n P F k e) := by
  intro j k hjk
  exact congr($(face_overlap hcof hfib D n P F G faceLaw j k hjk).map e.toPath)

def boundary : degree D (n + 3) ⥤
    target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) :=
  OrdinaryBarFreeBoundaryGluing.boundary (V := degree D (n + 2)) hcof hfib n
    (seed hcof hfib D n P F) (faceValues hcof hfib D n P F)
    (values_compatible hcof hfib D n P F G faceLaw)

lemma boundary_face (k : Fin (n + 3)) : boundary hcof hfib D n P F G faceLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
      face hcof hfib D n P F k := by
  rw [boundary, OrdinaryBarFreeBoundaryGluing.boundary_face]
  exact (Paths.lift_unique (V := degree D (n + 2)) _ (face hcof hfib D n P F k) rfl).symm

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary
