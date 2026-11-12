module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual coherent choices on the entire free resolution of the original base。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0180][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0180
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual coherent choices on the entire free resolution of the original base

No seed or higher coherence is assumed: the initial pair comes from the
existing cover and comparison, and all higher functors are constructed by
the relative iteration. This remains a resolution-indexed auxiliary object.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues
open OrdinaryBarFreeResolutionSeed
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def diagram (n : ℕ) :
    degree (D C) (n + 1) ⥤ target (C := C) hcof hfib (parameters P n) :=
  OrdinaryBarFreeResolutionTower.diagram hcof hfib (D C) P (seed C hcof hfib P) n

lemma diagram_zero : diagram (C := C) hcof hfib P 0 = zero C hcof hfib P := rfl

lemma diagram_one : diagram (C := C) hcof hfib P 1 = one C hcof hfib P := rfl

lemma diagram_face (n : ℕ) (i : Fin (n + 2)) : diagram (C := C) hcof hfib P (n + 1) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      fixedFace (D C) (n + 1) i ⋙ diagram hcof hfib P n :=
  OrdinaryBarFreeResolutionTower.diagram_face hcof hfib (D C) P (seed C hcof hfib P) n i

lemma diagram_degeneracy (n : ℕ) (i : Fin (n + 1)) : degeneracyFunctor (D C) n i ⋙
    diagram hcof hfib P (n + 1) = diagram hcof hfib P n ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) :=
  OrdinaryBarFreeResolutionTower.diagram_degeneracy hcof hfib (D C) P (seed C hcof hfib P) n i

def projection (n : ℕ) : degree (D C) (n + 1) ⥤ D C :=
  diagram hcof hfib P n ⋙ OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n)

/-- Iterated path composition followed by removal of the Hom-only lift. -/
def augmentation (n : ℕ) : degree (D C) (n + 1) ⥤ D C :=
  match n with
  | 0 => FreePathResolution.counit (degree (D C) 0) ⋙ down C
  | n + 1 => FreePathResolution.counit (degree (D C) (n + 1)) ⋙ augmentation n

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma fixedFace_last (n : ℕ) : fixedFace (D C) (n + 1) (Fin.last (n + 1)) =
    FreePathResolution.counit (degree (D C) (n + 1)) := by
  rw [fixedFace_eq]
  simp only [reverseFace, Fin.rev_last, faceFunctor, faceHom_zero]
  rfl

lemma projection_zero : projection (C := C) hcof hfib P 0 = augmentation (C := C) 0 := by
  change ((lower C ⋙ freeCover hcof hfib P) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (fst P point)) ⋙
      OrdinaryBarChoiceCategory.projection hcof hfib _ = _
  rw [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection,
    CategoryTheory.Functor.assoc, freeCover_projection, FreePathResolution.lift_identity]
  exact FreePathResolution.counit_naturality (down C)

lemma projection_eq_augmentation (n : ℕ) : projection (C := C) hcof hfib P n =
    augmentation (C := C) n := by
  induction n with
  | zero => exact projection_zero hcof hfib P
  | succ n ih =>
    have hh := congrArg
      (fun F => F ⋙ OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n))
      (diagram_face (C := C) hcof hfib P n (Fin.last (n + 1)))
    simp only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] at hh
    change projection hcof hfib P (n + 1) =
      fixedFace (D C) (n + 1) (Fin.last (n + 1)) ⋙ projection hcof hfib P n at hh
    rw [fixedFace_last, ih] at hh
    exact hh

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices
