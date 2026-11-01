module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeDiagramHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative interval comparisons of whole free diagrams。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0177][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0177
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative interval comparisons of whole free diagrams

The endpoints share their objects and base arrows. Prescribed generators
are fixed over the whole interval. No lifting for categories with relations
or simultaneous higher coherence is assumed.
-/

@[expose] public section
universe v u uV vV
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy
open OrdinaryBarFreeDiagramExtension
universe r

abbrev interval := SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1)

def boundaryZero {P : SSet.{r}} : P ⟶ P ⊗ (SSet.boundary 1).toSSet :=
  LargeParameterHomotopy.vertexSection P ≫ P ◁ SSet.boundary.ι (1 : Fin 2)

def boundaryOne {P : SSet.{r}} : P ⟶ P ⊗ (SSet.boundary 1).toSSet :=
  LargeParameterHomotopy.vertexSection P ≫ P ◁ SSet.boundary.ι (0 : Fin 2)

lemma boundaryZero_inclusion {P : SSet.{r}} :
    boundaryZero (P := P) ≫ P ◁ (SSet.boundary 1).ι = SSet.ι₀ := by
  rw [boundaryZero, Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι]
  exact LargeParameterHomotopy.section_zero P

lemma boundaryOne_inclusion {P : SSet.{r}} :
    boundaryOne (P := P) ≫ P ◁ (SSet.boundary 1).ι = SSet.ι₁ := by
  rw [boundaryOne, Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι]
  exact LargeParameterHomotopy.section_one P

lemma boundaryMap_self {P K : SSet.{r}} (s : P ⟶ K) :
    LargeParameterHomotopy.boundaryMap s s = fst P _ ≫ s := by
  apply (LargeParameterHomotopy.boundaryColimit P).hom_ext
  rintro ⟨i⟩
  cases i
  · change P ◁ SSet.boundary.ι (1 : Fin 2) ≫ _ = _
    rw [LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change P ◁ SSet.boundary.ι (0 : Fin 2) ≫ _ = _
    rw [LargeParameterHomotopy.boundaryMap_one]
    rfl

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {P : SSet.{max u v}}
  (φ : V ⥤q target (C := C) hcof hfib P)

lemma extension_eq {X Y : target (C := C) hcof hfib P} (a b : X ⟶ Y)
    (h : a = b) (hb : a.base = b.base) :
    a.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib hb = b.extension := by
  subst b
  rfl

lemma normalized_eq {X Y : target (C := C) hcof hfib P} (a b : X ⟶ Y)
    (hb : b.base = a.base) :
    (⟨a.base, b.extension ≫ OrdinaryBarChoiceComposition.relabel hcof hfib hb⟩ : X ⟶ Y) = b := by
  cases a with | mk af as =>
    cases b with | mk bf bs =>
      dsimp only at hb
      subst bf
      rfl

structure End where
  extension : {X Y : V} → (e : X ⟶ Y) →
    (P ⟶ OrdinaryBarRetractSystem.choices hcof hfib (φ.map e).base)

variable (ψ : End hcof hfib φ)

def endGenerators : V ⥤q target (C := C) hcof hfib P where
  obj X := φ.obj X
  map e := ⟨(φ.map e).base, ψ.extension e⟩

def boundaryGenerators : V ⥤q target (C := C) hcof hfib
    (P ⊗ (SSet.boundary 1).toSSet) where
  obj X := liftedObject hcof hfib (φ.obj X)
  map e := ⟨(φ.map e).base, LargeParameterHomotopy.boundaryMap (φ.map e).extension
    (ψ.extension e)⟩

lemma boundary_zero : Paths.lift (boundaryGenerators hcof hfib φ ψ) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (boundaryZero (P := P)) = Paths.lift φ := by
  refine Paths.ext_functor (F := Paths.lift (boundaryGenerators hcof hfib φ ψ) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (boundaryZero (P := P)))
    (G := Paths.lift φ) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, Paths.lift_toPath, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  have hm : boundaryZero (P := P) ≫ LargeParameterHomotopy.boundaryMap
      (φ.map e).extension (ψ.extension e) = (φ.map e).extension := by
    rw [boundaryZero, Category.assoc, LargeParameterHomotopy.boundaryMap_zero]
    rfl
  exact congrArg (fun s => (⟨(φ.map e).base, s⟩ : φ.obj X ⟶ φ.obj Y)) hm

lemma boundary_one : Paths.lift (boundaryGenerators hcof hfib φ ψ) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (boundaryOne (P := P)) =
      Paths.lift (endGenerators hcof hfib φ ψ) := by
  refine Paths.ext_functor (F := Paths.lift (boundaryGenerators hcof hfib φ ψ) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (boundaryOne (P := P)))
    (G := Paths.lift (endGenerators hcof hfib φ ψ)) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, Paths.lift_toPath, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  have hm : boundaryOne (P := P) ≫ LargeParameterHomotopy.boundaryMap
      (φ.map e).extension (ψ.extension e) =
      ψ.extension e := by
    rw [boundaryOne, Category.assoc, LargeParameterHomotopy.boundaryMap_one]
    rfl
  exact congrArg (fun s => (⟨(φ.map e).base, s⟩ : φ.obj X ⟶ φ.obj Y)) hm

structure Fixed where
  predicate : {X Y : V} → (X ⟶ Y) → Prop
  agree : ∀ {X Y : V} (e : X ⟶ Y), predicate e → ψ.extension e = (φ.map e).extension

variable (Q : Fixed hcof hfib φ ψ)

set_option maxHeartbeats 800000 in
-- Comparing the iterated lifted objects in this dependent restriction needs extra reduction.
def prescribed : OrdinaryBarRelativeFreeDiagramExtension.Prescribed hcof hfib
    (P ◁ (SSet.boundary 1).ι) (boundaryGenerators hcof hfib φ ψ) where
  fixed := Q.predicate
  value e _ := ⟨(φ.map e).base, fst P interval ≫ (φ.map e).extension⟩
  restriction {X Y} e he := by
    have hm : (P ◁ (SSet.boundary 1).ι) ≫ (fst P interval ≫ (φ.map e).extension) =
        LargeParameterHomotopy.boundaryMap (φ.map e).extension
          (ψ.extension e) := by
      rw [Q.agree e he, boundaryMap_self]
      rfl
    exact congrArg (OrdinaryBarChoiceCategory.Hom.mk
      (X := (boundaryGenerators hcof hfib φ ψ).obj X)
      (Y := (boundaryGenerators hcof hfib φ ψ).obj Y) (φ.map e).base) hm

def comparison : Paths V ⥤ target (C := C) hcof hfib (P ⊗ interval) :=
  OrdinaryBarRelativeFreeDiagramExtension.extend hcof hfib (P ◁ (SSet.boundary 1).ι)
    (boundaryGenerators hcof hfib φ ψ) (prescribed hcof hfib φ ψ Q)

lemma comparison_boundary : comparison hcof hfib φ ψ Q ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary 1).ι) =
      Paths.lift (boundaryGenerators hcof hfib φ ψ) :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_restriction hcof hfib _ _ _

lemma comparison_zero : comparison hcof hfib φ ψ Q ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = Paths.lift φ := by
  rw [← boundaryZero_inclusion, OrdinaryBarChoiceCategory.reindex_comp,
    ← CategoryTheory.Functor.assoc, comparison_boundary, boundary_zero]

lemma comparison_one : comparison hcof hfib φ ψ Q ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ =
      Paths.lift (endGenerators hcof hfib φ ψ) := by
  rw [← boundaryOne_inclusion, OrdinaryBarChoiceCategory.reindex_comp,
    ← CategoryTheory.Functor.assoc, comparison_boundary, boundary_one]

lemma comparison_fixed {X Y : V} (e : X ⟶ Y) (he : Q.predicate e) :
    (comparison hcof hfib φ ψ Q).map e.toPath =
      (OrdinaryBarChoiceCategory.reindex hcof hfib (fst P interval)).map (φ.map e) :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_fixed hcof hfib _ _ _ e he

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy
