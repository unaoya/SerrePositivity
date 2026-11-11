module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionSeed

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual initial coherent pair for the free choice resolution。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0187][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0187
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual initial coherent pair for the free choice resolution

Only Hom is lifted in the fixed-object presentation. Mapping the down
functor through one and two free-path constructions connects the existing
choice cover and comparison to the tower's actual initial pair.
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

abbrev point := SSet.stdSimplex.{r}.obj (SimplexCategory.mk 0)
abbrev interval := SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)

variable (C : Type u) [Category.{v} C]
abbrev D := Cᵒᵖ × C

def down : degree (D C) 0 ⥤ D C := ULiftHom.down.{v, u, u} (C := D C)

def lower : degree (D C) 1 ⥤ Paths (D C) := FreePathResolution.map (down C)

def upper : degree (D C) 2 ⥤ Paths (Paths (D C)) := FreePathResolution.map (lower C)

lemma fixedFace_zero : fixedFace (D C) 1 (0 : Fin 2) =
    FreePathResolution.map (FreePathResolution.counit (degree (D C) 0)) := by
  rw [fixedFace_eq]
  rfl

lemma fixedFace_one : fixedFace (D C) 1 (1 : Fin 2) =
    FreePathResolution.counit (degree (D C) 1) := by
  rw [fixedFace_eq]
  rfl

lemma upper_counit : upper C ⋙ FreePathResolution.counit (Paths (D C)) =
    fixedFace (D C) 1 (1 : Fin 2) ⋙ lower C := by
  rw [fixedFace_one]
  exact FreePathResolution.counit_naturality (lower C)

lemma upper_map_counit : upper C ⋙ FreePathResolution.map (FreePathResolution.counit (D C)) =
    fixedFace (D C) 1 (0 : Fin 2) ⋙ lower C := by
  rw [fixedFace_zero]
  change FreePathResolution.map (FreePathResolution.map (down C)) ⋙
      FreePathResolution.map (FreePathResolution.counit (D C)) =
    FreePathResolution.map (FreePathResolution.counit (degree (D C) 0)) ⋙
      FreePathResolution.map (down C)
  rw [← FreePathResolution.map_comp, FreePathResolution.counit_naturality,
    FreePathResolution.map_comp]

lemma upper_degeneracy : degeneracyFunctor (D C) 0 0 ⋙ upper C =
    lower C ⋙ FreePathResolution.duplicate (D C) := by
  rw [degeneracyFunctor_zero]
  exact (FreePathResolution.duplicate_naturality (down C)).symm

variable [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def zero : degree (D C) 1 ⥤ target (C := C) hcof hfib (parameters P 0) :=
  (lower C ⋙ freeCover hcof hfib P) ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (fst P point)

def one : degree (D C) 2 ⥤ target (C := C) hcof hfib (parameters P 1) :=
  upper C ⋙ OrdinaryBarFreeResolutionComparison.comparison hcof hfib P

lemma upper_faceZero : upper C ⋙ OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P =
    fixedFace (D C) 1 (1 : Fin 2) ⋙ (lower C ⋙ freeCover hcof hfib P) := by
  rw [OrdinaryBarFreeResolutionFaces.faceZero, ← CategoryTheory.Functor.assoc, upper_counit,
    CategoryTheory.Functor.assoc]

lemma upper_faceOne : upper C ⋙ OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P =
    fixedFace (D C) 1 (0 : Fin 2) ⋙ (lower C ⋙ freeCover hcof hfib P) := by
  rw [OrdinaryBarFreeResolutionFaces.faceOne, ← CategoryTheory.Functor.assoc, upper_map_counit,
    CategoryTheory.Functor.assoc]

lemma one_face0 : one C hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (0 : Fin 2)) =
      fixedFace (D C) 1 (0 : Fin 2) ⋙ zero C hcof hfib P := by
  rw [one, CategoryTheory.Functor.assoc, OrdinaryBarChoiceTriangleGluing.tensor_face_zero,
    OrdinaryBarChoiceCategory.reindex_comp]
  rw [← CategoryTheory.Functor.assoc (OrdinaryBarFreeResolutionComparison.comparison hcof hfib P),
    OrdinaryBarFreeResolutionComparison.comparison_one, ← CategoryTheory.Functor.assoc,
    upper_faceOne, CategoryTheory.Functor.assoc]
  rfl

lemma one_face1 : one C hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (1 : Fin 2)) =
      fixedFace (D C) 1 (1 : Fin 2) ⋙ zero C hcof hfib P := by
  rw [one, CategoryTheory.Functor.assoc, OrdinaryBarChoiceTriangleGluing.tensor_face_one,
    OrdinaryBarChoiceCategory.reindex_comp]
  rw [← CategoryTheory.Functor.assoc (OrdinaryBarFreeResolutionComparison.comparison hcof hfib P),
    OrdinaryBarFreeResolutionComparison.comparison_zero, ← CategoryTheory.Functor.assoc,
    upper_faceZero, CategoryTheory.Functor.assoc]
  rfl

lemma one_degeneracy : degeneracyFunctor (D C) 0 0 ⋙ one C hcof hfib P =
    zero C hcof hfib P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma 0 0) := by
  rw [one, ← CategoryTheory.Functor.assoc, upper_degeneracy, CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionComparison.comparison_degeneracy]
  rw [zero, CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    whiskerLeft_fst]
  rfl

/-- The initial pair is constructed from the original cover and comparison. -/
def seed : OrdinaryBarFreeResolutionTower.Seed (C := C) hcof hfib (D C) P where
  current := one C hcof hfib P
  previous := zero C hcof hfib P
  faceLaw i := by
    fin_cases i
    · exact one_face0 C hcof hfib P
    · exact one_face1 C hcof hfib P
  degeneracyLaw i := by
    fin_cases i
    exact one_degeneracy C hcof hfib P

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed
