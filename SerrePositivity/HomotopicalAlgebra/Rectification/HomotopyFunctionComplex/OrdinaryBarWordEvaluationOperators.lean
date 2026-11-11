module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordExt
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordAction
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationSourceMap

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordEvaluationOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All free-resolution faces and degeneracies commute with the actual word evaluation。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0242][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0242
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All free-resolution faces and degeneracies commute with the actual word evaluation
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarWordPresentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

lemma evaluation_face (i : Fin (n + 2)) (k : SimplexCategoryᵒᵖ) (t : (parameters P n).obj k) :
    RetractWords.map (FreeGeneratorFaces.fixedFace (D C) (n + 1) i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P n k t =
    largeEvaluation (C := C) hcof hfib P (n + 1) k ((P ◁ SSet.stdSimplex.δ i).app k t) := by
  apply RetractWords.functor_ext_generators
    (C := degree (D C) (n + 2)) (M := WordSegment.degree.{max u v} k)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change RetractWords.Edge _ _ X Y at e
    cases e with
    | source f =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_source,
        RetractWords.Realization.functor_source]
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro x
      change (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
        ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).map f)).app k (x, t) =
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P (n + 1) f).app k
            (x, (P ◁ SSet.stdSimplex.δ i).app k t)
      exact (types_congr_hom (congr_app
        (OrdinaryBarFreeAmbientFamilies.family_face hcof hfib P n i f) k) (x, t)).symm
    | word X w =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_word,
        RetractWords.Realization.functor_word]
      rfl
    | section_ X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_section,
        RetractWords.Realization.functor_section]
      rfl
    | projection X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_projection,
        RetractWords.Realization.functor_projection]
      rfl

lemma evaluation_degeneracy (i : Fin (n + 1)) (k : SimplexCategoryᵒᵖ)
    (t : (parameters P (n + 1)).obj k) :
    RetractWords.map (degeneracyFunctor (D C) n i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P (n + 1) k t =
    largeEvaluation (C := C) hcof hfib P n k
      ((P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i).app k t) := by
  apply RetractWords.functor_ext_generators
    (C := degree (D C) (n + 1)) (M := WordSegment.degree.{max u v} k)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change RetractWords.Edge _ _ X Y at e
    cases e with
    | source f =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_source,
        RetractWords.Realization.functor_source]
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro x
      change (OrdinaryBarFreeAmbientFamilies.family hcof hfib P (n + 1)
        ((degeneracyFunctor (D C) n i).map f)).app k (x, t) =
          (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f).app k
            (x, (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i).app k t)
      exact types_congr_hom (congr_app
        (OrdinaryBarFreeAmbientFamilies.family_degeneracy hcof hfib P n i f) k) (x, t)
    | word X w =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_word,
        RetractWords.Realization.functor_word]
      rfl
    | section_ X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_section,
        RetractWords.Realization.functor_section]
      rfl
    | projection X =>
      simp only [CategoryTheory.Functor.comp_map, RetractWords.map_projection,
        RetractWords.Realization.functor_projection]
      rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators
