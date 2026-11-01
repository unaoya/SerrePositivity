module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeDegeneracyExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative free extension preserving every degeneracy in arbitrary degree。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0175][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0175
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative free extension preserving every degeneracy in arbitrary degree

Compatible values on double-degeneracy intersections descend to a single
Prescribed datum. Its relative extension retains the whole boundary and all
actual free-resolution degeneracy functors. Boundary data and compatible
values are inputs; their inductive construction is a further step.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension
open OrdinaryBarFreeDiagramExtension FreeGeneratorDegeneracies FreeGeneratorCategories
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ)
  {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]
  (φ : degree D (n + 2) ⥤q target (C := C) hcof hfib U)

abbrev Value := (i : Fin (n + 2)) → {X Y : D} → hom (n + 1) X Y →
  (liftedObject hcof hfib (T := T) (φ.obj X) ⟶ liftedObject hcof hfib (T := T) (φ.obj Y))

variable (value : Value hcof hfib D n φ)
  (compatible : ∀ X Y : D, FreeGeneratorLatchingValues.Compatible n
    (fun i (p : hom (n + 1) X Y) => value i p))
  (restriction : ∀ (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y),
    (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (value i p) =
      φ.map (degeneracy (n + 1) i p))

def prescribed : OrdinaryBarRelativeFreeDiagramExtension.Prescribed
    (V := degree D (n + 2)) hcof hfib j φ where
  fixed e := FreeGeneratorLatchingValues.Fixed n e
  value e he := FreeGeneratorLatchingValues.desc n (fun i p => value i p) e he
  restriction e he := FreeGeneratorLatchingValues.desc_restriction n (fun i p => value i p)
    (fun f => (OrdinaryBarChoiceCategory.reindex hcof hfib j).map f)
    (fun e => φ.map e) (fun i p => restriction i p) e he

def filler : degree D (n + 3) ⥤ target (C := C) hcof hfib T :=
  OrdinaryBarRelativeFreeDiagramExtension.extend (V := degree D (n + 2)) hcof hfib j φ
    (prescribed hcof hfib D n j φ value restriction)

lemma filler_boundary : filler hcof hfib D n j φ value restriction ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib j = Paths.lift (V := degree D (n + 2)) φ :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_restriction (V := degree D (n + 2)) hcof hfib j φ _

lemma filler_projection : filler hcof hfib D n j φ value restriction ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib T =
      Paths.lift (V := degree D (n + 2)) φ ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib U :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_projection
    (V := degree D (n + 2)) hcof hfib j φ _

include compatible in
lemma filler_fixed (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y) :
    (filler hcof hfib D n j φ value restriction).map
      (singleton (n + 2) (degeneracy (n + 1) i p)) = value i p := by
  change (OrdinaryBarRelativeFreeDiagramExtension.extend (V := degree D (n + 2)) hcof hfib j φ
    (prescribed hcof hfib D n j φ value restriction)).map
      (Quiver.Hom.toPath (V := degree D (n + 2)) (degeneracy (n + 1) i p)) = _
  rw [OrdinaryBarRelativeFreeDiagramExtension.extend_fixed (V := degree D (n + 2)) hcof hfib j φ _ _
    (FreeGeneratorLatchingValues.fixed_degeneracy n i p)]
  exact FreeGeneratorLatchingValues.desc_degeneracy n _ (compatible X Y) i p _

def degenerateGenerators (i : Fin (n + 2)) :
    degree D (n + 1) ⥤q target (C := C) hcof hfib T where
  obj X := liftedObject hcof hfib (T := T) (φ.obj X)
  map p := value i p

def degenerateDiagram (i : Fin (n + 2)) : degree D (n + 2) ⥤ target (C := C) hcof hfib T :=
  Paths.lift (V := degree D (n + 1)) (degenerateGenerators hcof hfib D n φ value i)

include restriction in
omit [Mono j] in
lemma degenerateDiagram_boundary (i : Fin (n + 2)) :
    degenerateDiagram hcof hfib D n φ value i ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j =
      degeneracyFunctor D (n + 1) i ⋙ Paths.lift (V := degree D (n + 2)) φ := by
  refine Paths.ext_functor (V := degree D (n + 1))
    (F := degenerateDiagram hcof hfib D n φ value i ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib j)
    (G := degeneracyFunctor D (n + 1) i ⋙ Paths.lift (V := degree D (n + 2)) φ) rfl ?_
  intro X Y p
  simp only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id,
    degenerateDiagram, Paths.lift_toPath]
  change (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (value i p) =
    (Paths.lift (V := degree D (n + 2)) φ).map
      (Quiver.Hom.toPath (V := degree D (n + 2)) (degeneracy (n + 1) i p))
  rw [Paths.lift_toPath]
  exact restriction i p

include compatible in
lemma filler_degeneracy (i : Fin (n + 2)) :
    degeneracyFunctor D (n + 1) i ⋙ filler hcof hfib D n j φ value restriction =
      degenerateDiagram hcof hfib D n φ value i := by
  refine Paths.ext_functor (V := degree D (n + 1))
    (F := degeneracyFunctor D (n + 1) i ⋙ filler hcof hfib D n j φ value restriction)
    (G := degenerateDiagram hcof hfib D n φ value i) rfl ?_
  intro X Y p
  simp only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id,
    degenerateDiagram, Paths.lift_toPath]
  change (filler hcof hfib D n j φ value restriction).map
    (singleton (n + 2) (degeneracy (n + 1) i p)) = value i p
  exact filler_fixed hcof hfib D n j φ value compatible restriction i p

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension
