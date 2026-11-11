module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreeGeneratorMixedOperators
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ReversedSimplexParameters

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionMixedFaces

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Every facet of a prescribed degenerate choice diagram。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0185][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0185
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Every facet of a prescribed degenerate choice diagram

The lower face and degeneracy equations imply that the next source
boundary and the prescribed degenerate diagram agree on every facet.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces
open FreeGeneratorCategories FreeGeneratorMixedOperators OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (n + 1) i ⋙ G)
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i))

include faceLaw in
lemma raw_face_law (i : Fin (n + 2)) :
    F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta n i) =
      rawFace D (n + 1) i ⋙ G := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_eq]
  exact faceLaw i.rev

lemma diagram_face (j : Fin (n + 2)) (i : Fin (n + 3)) :
    diagram hcof hfib D n P F j ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) i) =
    F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma (n + 1) j)) := by
  rw [diagram, CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← whiskerLeft_comp]

lemma facet_self (j : Fin (n + 2)) :
    degeneracyFunctor D (n + 1) j ⋙ (rawFace D (n + 2) j.castSucc ⋙ F) =
      diagram hcof hfib D n P F j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) j.castSucc) := by
  rw [← CategoryTheory.Functor.assoc, degeneracy_face_self, CategoryTheory.Functor.id_comp,
    diagram_face, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_sigma_self, MonoidalCategory.whiskerLeft_id,
    OrdinaryBarChoiceCategory.reindex_id, CategoryTheory.Functor.comp_id]

lemma facet_succ (j : Fin (n + 2)) :
    degeneracyFunctor D (n + 1) j ⋙ (rawFace D (n + 2) j.succ ⋙ F) =
      diagram hcof hfib D n P F j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) j.succ) := by
  rw [← CategoryTheory.Functor.assoc, degeneracy_face_succ, CategoryTheory.Functor.id_comp,
    diagram_face, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_sigma_succ, MonoidalCategory.whiskerLeft_id,
    OrdinaryBarChoiceCategory.reindex_id, CategoryTheory.Functor.comp_id]

include faceLaw degeneracyLaw in
lemma facet_le (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    degeneracyFunctor D (n + 1) j.succ ⋙ (rawFace D (n + 2) i.castSucc ⋙ F) =
      diagram hcof hfib D n P F j.succ ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) i.castSucc) := by
  rw [diagram_face, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_sigma_le n i j h, ← CategoryTheory.Functor.assoc,
    degeneracy_face_le D n i j h, CategoryTheory.Functor.assoc, degeneracyLaw j,
    ← CategoryTheory.Functor.assoc, ← raw_face_law hcof hfib D n P F G faceLaw i,
    CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← whiskerLeft_comp]

include faceLaw degeneracyLaw in
lemma facet_gt (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    degeneracyFunctor D (n + 1) j.castSucc ⋙ (rawFace D (n + 2) i.succ ⋙ F) =
      diagram hcof hfib D n P F j.castSucc ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) i.succ) := by
  rw [diagram_face, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta_sigma_gt n i j h, ← CategoryTheory.Functor.assoc,
    degeneracy_face_gt D n i j h, CategoryTheory.Functor.assoc, degeneracyLaw j,
    ← CategoryTheory.Functor.assoc, ← raw_face_law hcof hfib D n P F G faceLaw i,
    CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← whiskerLeft_comp]

include faceLaw degeneracyLaw in
lemma facet_equation (j : Fin (n + 2)) (i : Fin (n + 3)) :
    degeneracyFunctor D (n + 1) j ⋙ (rawFace D (n + 2) i ⋙ F) =
      diagram hcof hfib D n P F j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.delta (n + 1) i) := by
  rcases lt_trichotomy i j.castSucc with hlt | rfl | hgt
  · change i.val < j.val at hlt
    let a : Fin (n + 2) := ⟨i.val, by omega⟩
    let b : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have ha : a.castSucc = i := Fin.ext rfl
    have hb : b.succ = j := Fin.ext (by dsimp [b]; omega)
    have hab : a ≤ b.castSucc := by change i.val ≤ j.val - 1; omega
    rw [← ha, ← hb]
    exact facet_le hcof hfib D n P F G faceLaw degeneracyLaw a b hab
  · exact facet_self hcof hfib D n P F j
  · change j.val < i.val at hgt
    by_cases heq : i = j.succ
    · subst i; exact facet_succ hcof hfib D n P F j
    · have hne : i.val ≠ j.val + 1 := fun hh => heq (Fin.ext hh)
      have hbig : j.val + 1 < i.val := by omega
      let a : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      let b : Fin (n + 1) := ⟨j.val, by omega⟩
      have ha : a.succ = i := Fin.ext (by dsimp [a]; omega)
      have hb : b.castSucc = j := Fin.ext rfl
      have hab : b.castSucc < a := by change j.val < i.val - 1; omega
      rw [← ha, ← hb]
      exact facet_gt hcof hfib D n P F G faceLaw degeneracyLaw a b hab

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces
