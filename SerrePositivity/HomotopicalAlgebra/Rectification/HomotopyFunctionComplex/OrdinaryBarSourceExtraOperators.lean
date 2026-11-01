module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceOperators
public import SerrePositivity.CategoryTheory.Quiver.PathObjectTransport

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceExtraOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Exact-object face operators on singleton free paths。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0226][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0226
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Exact-object face operators on singleton free paths
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C]

def fixedForwardFace (n : ℕ) (i : Fin (n + 1)) : degree (D C) (n + 1) ⥤ degree (D C) n :=
  (faceFunctor (D C) n i).copyObj (fun X => X) (fun X => eqToIso (faceFunctor_obj (D C) n i X))

lemma fixedForwardFace_eq (n : ℕ) (i : Fin (n + 1)) :
    fixedForwardFace C n i = faceFunctor (D C) n i := by
  refine CategoryTheory.Functor.ext (fun X => (faceFunctor_obj (D C) n i X).symm) ?_
  intro X Y f
  simp [fixedForwardFace, Functor.copyObj]

lemma literal_forward_face {n : ℕ} (i : Fin (n + 2)) :
    OrdinaryBarFixedSource.literalMap C (SimplexCategory.rev.map (SimplexCategory.δ i)).op =
      fixedForwardFace C (n + 1) i :=
  (OrdinaryBarSourceOperators.forward_face C i).trans (fixedForwardFace_eq C (n + 1) i).symm

lemma forward_face_map {n : ℕ} (i : Fin (n + 2)) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom (n + 2) X Y) :
    (OrdinaryBarFixedSource.literalMap C (SimplexCategory.rev.map (SimplexCategory.δ i)).op).map
        (X := X) (Y := Y) p = (fixedForwardFace C (n + 1) i).map p := by
  exact congr($(literal_forward_face C i).map p)

lemma forward_degeneracy_map {n : ℕ} (i : Fin (n + 1)) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    (OrdinaryBarFixedSource.literalMap C (SimplexCategory.rev.map (SimplexCategory.σ i)).op).map
        (X := X) (Y := Y) p = (degeneracyFunctor (D C) n i).map p := by
  exact congr($(OrdinaryBarSourceOperators.forward_degeneracy C i).map p)

lemma forward_hom_face {n : ℕ} (i : Fin (n + 2)) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom (n + 2) X Y) :
    (OrdinaryBarSourceOperators.forwardHom C X Y).δ i p =
      (fixedForwardFace C (n + 1) i).map p := forward_face_map C i p

lemma face_succ_singleton (n : ℕ) (i : Fin (n + 1)) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    (fixedForwardFace C (n + 1) i.succ).map (FreeGeneratorDegeneracies.singleton (n + 1) p) =
      FreeGeneratorDegeneracies.singleton n ((fixedForwardFace C n i).map p) := by
  exact QuiverPaths.map_copyObj_generator (faceFunctor (D C) n i) (fun X => X)
    (fun X => faceFunctor_obj (D C) n i X) p

lemma face_zero_singleton (n : ℕ) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom n X Y) :
    (fixedForwardFace C n 0).map (FreeGeneratorDegeneracies.singleton n p) = p := by
  cases n with
  | zero => exact QuiverPaths.counit_copy_singleton (D := degree (D C) 0) p
  | succ n => exact QuiverPaths.counit_copy_singleton (D := degree (D C) (n + 1)) p

lemma degeneracy_succ_singleton (n : ℕ) (i : Fin (n + 1)) {X Y : D C}
    (p : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    (degeneracyFunctor (D C) (n + 1) i.succ).map
        (FreeGeneratorDegeneracies.singleton (n + 1) p) =
      FreeGeneratorDegeneracies.singleton (n + 2) ((degeneracyFunctor (D C) n i).map p) := rfl

lemma projection_zero_map {X Y : D C} (p : FreeGeneratorDegeneracies.hom 1 X Y) :
    (OrdinaryBarFixedAugmentation.sourceProjection C
      (Opposite.op (SimplexCategory.mk 0))).map p = ((fixedForwardFace C 0 0).map p).down := by
  have h : OrdinaryBarFixedAugmentation.sourceProjection C
      (Opposite.op (SimplexCategory.mk 0)) =
        fixedForwardFace C 0 0 ⋙ ULiftHom.down.{v, u, u} (C := D C) := by
    rw [OrdinaryBarFixedAugmentation.sourceProjection_eq, OrdinaryBarFixedSource.projection_eq,
      fixedForwardFace_eq]
    rfl
  exact congr($(h).map p)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators
