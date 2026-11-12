module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryMappingClassLabel
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionBar
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallDiagramQuotient
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# 中断した任意モデル源への一般化：OrdinaryBarMappingClasses

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A natural ordinary mapping-class label on the whole resolution bar。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0199][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0199
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A natural ordinary mapping-class label on the whole resolution bar

The label kernel is a small coarse quotient and a bound on admissible
identifications. No finite-boundary lifting or preservation of higher
homotopy is asserted for this coarse quotient.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingClasses
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

def augmentation : OrdinaryResolutionBar.functor (C := C) ⟶
    LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  BarConstruction.relativeAugmentation OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw (OrdinaryMappingClassLabel.comparison Q)

def label (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (x : (OrdinaryResolutionBar.functor.obj b).obj n) : LocalizedHomDiagram.value Q b :=
  (((augmentation Q).app b).app n x).down

def point (R : OrdinaryResolutionPairs.Index (C := C)) (n : SimplexCategoryᵒᵖ)
    (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    CostructuredArrow (BarConstruction.elementProjection OrdinaryResolutionPairs.projection
      OrdinaryResolutionPairs.raw n) (OrdinaryResolutionPairs.projection.obj R) :=
  CostructuredArrow.mk (Y := (OrdinaryResolutionPairs.raw.flip.obj n).elementsMk R f) (𝟙 _)

/-- This is simplicial for a fixed resolution pair; base naturality is not asserted. -/
def entry (R : OrdinaryResolutionPairs.Index (C := C)) :
    SSet.uliftFunctor.{max u v, v}.obj (OrdinaryResolutionPairs.raw.obj R) ⟶
      OrdinaryResolutionBar.functor.obj (OrdinaryResolutionPairs.projection.obj R) where
  app n := ↾fun x => (Functor.const (Fin (n.unop.len + 1))).obj (point R n x.down)
  naturality {_ _} _ := rfl

lemma entry_label (R : OrdinaryResolutionPairs.Index (C := C)) (n : SimplexCategoryᵒᵖ)
    (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    label Q (OrdinaryResolutionPairs.projection.obj R) n ((entry R).app n ⟨f⟩) =
      OrdinaryMappingClassLabel.label Q R n f := by
  change (LocalizedHomDiagram.types Q).map (𝟙 _) (OrdinaryMappingClassLabel.label Q R n f) = _
  rw [(LocalizedHomDiagram.types Q).map_id]
  rfl

lemma entry_augmentation (R : OrdinaryResolutionPairs.Index (C := C)) :
    entry R ≫ (augmentation Q).app (OrdinaryResolutionPairs.projection.obj R) =
      SSet.uliftFunctor.{max u v, v}.map ((OrdinaryMappingClassLabel.comparison Q).app R) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  exact entry_label Q R n x.down

lemma label_operator (b : Cᵒᵖ × C) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : (OrdinaryResolutionBar.functor.obj b).obj n) :
    label Q b m ((OrdinaryResolutionBar.functor.obj b).map θ x) = label Q b n x :=
  congrArg ULift.down (types_congr_hom ((augmentation Q).app b |>.naturality θ) x)

lemma label_base {b c : Cᵒᵖ × C} (f : b ⟶ c) (n : SimplexCategoryᵒᵖ)
    (x : (OrdinaryResolutionBar.functor.obj b).obj n) :
    label Q c n ((OrdinaryResolutionBar.functor.map f).app n x) =
      (LocalizedHomDiagram.types Q).map f (label Q b n x) :=
  congrArg ULift.down (types_congr_hom (congr_app ((augmentation Q).naturality f) n) x)

def piZeroLabel (b : Cᵒᵖ × C) :
    SSet.π₀ (OrdinaryResolutionBar.functor.obj b) → LocalizedHomDiagram.value Q b :=
  SSet.π₀.lift (label Q b (Opposite.op (SimplexCategory.mk 0))) (fun {x y} e => by
    calc
      _ = label Q b _ ((OrdinaryResolutionBar.functor.obj b).δ 1 e.edge) :=
        congrArg (label Q b _) e.src_eq.symm
      _ = label Q b _ e.edge :=
        label_operator Q b (SimplexCategory.δ (1 : Fin 2)).op e.edge
      _ = label Q b _ ((OrdinaryResolutionBar.functor.obj b).δ 0 e.edge) :=
        (label_operator Q b (SimplexCategory.δ (0 : Fin 2)).op e.edge).symm
      _ = _ := congrArg (label Q b _) e.tgt_eq)

lemma piZeroLabel_mk (b : Cᵒᵖ × C)
    (x : (OrdinaryResolutionBar.functor.obj b).obj (Opposite.op (SimplexCategory.mk 0))) :
    piZeroLabel Q b (SSet.π₀.mk x) = label Q b _ x := rfl

lemma piZeroLabel_base {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroLabel Q c (SSet.mapπ₀ (OrdinaryResolutionBar.functor.map f) z) =
      (LocalizedHomDiagram.types Q).map f (piZeroLabel Q b z) := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  exact label_base Q f _ x

def kernel : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel (augmentation Q)

lemma kernel_iff (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (x y : (OrdinaryResolutionBar.functor.obj b).obj n) :
    (kernel Q).rel b n x y ↔ label Q b n x = label Q b n y :=
  ⟨congrArg ULift.down, ULift.ext⟩

lemma kernel_small (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((kernel Q).rel b n)) := by
  have : Small.{v} (((LocalizedHomDiagram.spaces Q ⋙
      SSet.uliftFunctor.{max u v, v}).obj b).obj n) :=
    small_of_injective (f := ULift.down) ULift.down_injective
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel_small (augmentation Q) b n

lemma quotient_eq_iff_label_eq (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (x y : (OrdinaryResolutionBar.functor.obj b).obj n) :
    Quotient.mk ((kernel Q).rel b n) x = Quotient.mk ((kernel Q).rel b n) y ↔
      label Q b n x = label Q b n y :=
  ⟨fun h => (kernel_iff Q b n x y).mp (Quotient.exact h),
    fun h => Quotient.sound ((kernel_iff Q b n x y).mpr h)⟩

/-- Any finer stable relation preserving these labels retains the ordinary class map. -/
def descend (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)))
    (hR : ∀ b n {x y}, (R.rel b n).r x y → label Q b n x = label Q b n y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.functor R ⟶
      LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.descend R (augmentation Q) (fun b n {_ _} h => ULift.ext (hR b n h))

lemma descend_factorization
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)))
    (hR : ∀ b n {x y}, (R.rel b n).r x y → label Q b n x = label Q b n y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection R ≫ descend Q R hR = augmentation Q := rfl

/-- This is a coarse mapping-class quotient, not the homotopy function complex. -/
abbrev coarseQuotient : Cᵒᵖ × C ⥤ SSet.{v} :=
  SmallDiagramQuotient.functor (kernel Q) (kernel_small Q)

abbrev coarseProjection : OrdinaryResolutionBar.functor (C := C) ⟶
    coarseQuotient Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  SmallDiagramQuotient.projection (kernel Q) (kernel_small Q)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingClasses
