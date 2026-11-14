module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.ReversedDegeneracies

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionDegeneracyValues

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual degenerate values and their all-degree intersection compatibility。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0182][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0182
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual degenerate values and their all-degree intersection compatibility

The values are reindexings of the preceding choice functor along the reversed
simplex degeneracies. Their agreement on every double-degeneracy overlap
follows from the preceding functor's degeneracy equations.
-/

@[expose] public section
universe v u r vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues
open FreeGeneratorCategories FreeGeneratorDegeneracies OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i))

def diagram (i : Fin (n + 2)) :
    degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 2)) :=
  F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma (n + 1) i)

include degeneracyLaw in
lemma diagram_overlap (i j : Fin (n + 1)) (h : i ≤ j) :
    degeneracyFunctor D n j ⋙ diagram hcof hfib D n P F i.castSucc =
      degeneracyFunctor D n i ⋙ diagram hcof hfib D n P F j.succ := by
  unfold diagram
  rw [← CategoryTheory.Functor.assoc, ← CategoryTheory.Functor.assoc,
    degeneracyLaw j, degeneracyLaw i, CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    ← OrdinaryBarChoiceCategory.reindex_comp, ← OrdinaryBarChoiceCategory.reindex_comp,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensor_sigma_sigma P n i j h]

abbrev object (X : D) : target (C := C) hcof hfib (parameters P (n + 2)) :=
  ⟨(F.obj X).base⟩

def value (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y) :
    object hcof hfib D n P F X ⟶ object hcof hfib D n P F Y :=
  (diagram hcof hfib D n P F i).map (singleton (n + 1) p)

include degeneracyLaw in
lemma values_compatible (X Y : D) : FreeGeneratorLatchingValues.Compatible n
    (fun i (p : hom (n + 1) X Y) => value hcof hfib D n P F i p) := by
  intro i j h r
  have hh := congr($(diagram_overlap hcof hfib D n P F G degeneracyLaw i j h).map
    (singleton n r))
  simpa only [CategoryTheory.Functor.comp_map, degeneracyFunctor_generator, value] using hh

def generators (i : Fin (n + 2)) :
    degree D (n + 1) ⥤q target (C := C) hcof hfib (parameters P (n + 2)) where
  obj X := object hcof hfib D n P F X
  map p := value hcof hfib D n P F i p

lemma diagram_from_generators (i : Fin (n + 2)) :
    Paths.lift (V := degree D (n + 1)) (generators hcof hfib D n P F i) =
      diagram hcof hfib D n P F i :=
  (Paths.lift_unique (V := degree D (n + 1)) _ (diagram hcof hfib D n P F i) rfl).symm

def prescribedValue {X Y : D} (e : hom (n + 2) X Y)
    (he : FreeGeneratorLatchingValues.Fixed n e) :
    object hcof hfib D n P F X ⟶ object hcof hfib D n P F Y :=
  FreeGeneratorLatchingValues.desc n (fun i p => value hcof hfib D n P F i p) e he

include degeneracyLaw in
lemma prescribedValue_degeneracy (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y)
    (he : FreeGeneratorLatchingValues.Fixed n (degeneracy (n + 1) i p)) :
    prescribedValue hcof hfib D n P F (degeneracy (n + 1) i p) he =
      value hcof hfib D n P F i p :=
  FreeGeneratorLatchingValues.desc_degeneracy n _
    (values_compatible hcof hfib D n P F G degeneracyLaw X Y) i p he

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues
