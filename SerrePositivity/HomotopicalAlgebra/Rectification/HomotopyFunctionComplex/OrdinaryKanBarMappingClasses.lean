module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteKanExtension
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarPiZero
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarBaseInvariance

/-!
# 中断した任意モデル源への一般化：OrdinaryKanBarMappingClasses

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Natural ordinary morphism labels on the actual Kan resolution bar。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0248][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0248
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Natural ordinary morphism labels on the actual Kan resolution bar

Discrete extension is unique, so the whole comparison remains natural.
The values are large Kan sets; a homotopy-preserving small quotient has
not been constructed by this file.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev functor : Cᵒᵖ × C ⥤ SSet.{max u v} :=
  OrdinaryResolutionBar.functor ⋙ AnodyneKanReplacement.functor

abbrev unit : OrdinaryResolutionBar.functor (C := C) ⟶ functor :=
  Functor.whiskerLeft OrdinaryResolutionBar.functor AnodyneKanReplacement.unit

lemma terminal_rlp (b : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor (C := C)).obj b)) :=
  AnodyneKanReplacement.terminal_rlp _

lemma unit_piZero_bijective (b : Cᵒᵖ × C) :
    Function.Bijective (SSet.mapπ₀ ((unit (C := C)).app b)) :=
  PiZeroLocalization.piZero_bijective _
    (Localization.inverts AnodyneHomotopy.anodyneQ _ _
      (AnodyneKanReplacement.unit_anodyne _))

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

def augmentation : functor (C := C) ⟶
    LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  DiscreteKanExtension.naturalExtension
    (T := LocalizedHomDiagram.types Q ⋙ CategoryTheory.uliftFunctor.{max u v, v})
    (OrdinaryBarMappingClasses.augmentation Q)

lemma unit_augmentation : unit ≫ augmentation Q = OrdinaryBarMappingClasses.augmentation Q :=
  DiscreteKanExtension.naturalExtension_fac _

lemma augmentation_unique
    (a : functor (C := C) ⟶ LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v})
    (ha : unit ≫ a = OrdinaryBarMappingClasses.augmentation Q) : a = augmentation Q :=
  DiscreteKanExtension.naturalExtension_unique
    (T := LocalizedHomDiagram.types Q ⋙ CategoryTheory.uliftFunctor.{max u v, v}) _ a ha

def piZeroLabel (b : Cᵒᵖ × C) :
    SSet.π₀ (functor.obj b) → LocalizedHomDiagram.value Q b :=
  fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents
    (show functor.obj b ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (ULift.{max u v, v} (LocalizedHomDiagram.value Q b)) from
        (augmentation Q).app b) z).down

lemma piZeroLabel_unit (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroLabel Q b (SSet.mapπ₀ (unit.app b) z) =
      OrdinaryBarMappingClasses.piZeroLabel Q b z := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  exact congrArg ULift.down
    (types_congr_hom (congr_app (congr_app (unit_augmentation Q) b)
      (Opposite.op (SimplexCategory.mk 0))) x)

lemma piZeroLabel_base {b c : Cᵒᵖ × C} (f : b ⟶ c) (z : SSet.π₀ (functor.obj b)) :
    piZeroLabel Q c (SSet.mapπ₀ (functor.map f) z) =
      (LocalizedHomDiagram.types Q).map f (piZeroLabel Q b z) := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  exact congrArg ULift.down (types_congr_hom
    (congr_app ((augmentation Q).naturality f) (Opposite.op (SimplexCategory.mk 0))) x)

def kernel : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (functor (C := C)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel (augmentation Q)

lemma kernel_small (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((kernel Q).rel b n)) := by
  have : Small.{v} (((LocalizedHomDiagram.spaces Q ⋙
      SSet.uliftFunctor.{max u v, v}).obj b).obj n) :=
    small_of_injective (f := ULift.down) ULift.down_injective
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel_small (augmentation Q) b n

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma piZeroLabel_bijective (b : Cᵒᵖ × C) : Function.Bijective (piZeroLabel Q b) := by
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := (unit_piZero_bijective b).surjective x
    obtain ⟨y, rfl⟩ := (unit_piZero_bijective b).surjective y
    rw [piZeroLabel_unit, piZeroLabel_unit] at h
    exact congrArg (SSet.mapπ₀ (unit.app b))
      (OrdinaryBarPiZero.piZeroLabel_injective hcof hfib Q b h)
  · intro z
    obtain ⟨x, hx⟩ := OrdinaryBarLabelSurjectivity.piZeroLabel_surjective Q b z
    exact ⟨SSet.mapπ₀ (unit.app b) x, (piZeroLabel_unit Q b x).trans hx⟩

def piZeroEquiv (b : Cᵒᵖ × C) :
    SSet.π₀ (functor.obj b) ≃ (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  (Equiv.ofBijective _ (piZeroLabel_bijective Q hcof hfib b)).trans
    (LocalizedHomDiagram.equiv Q b)

lemma piZeroEquiv_unit (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroEquiv Q hcof hfib b (SSet.mapπ₀ (unit.app b) z) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z := by
  change LocalizedHomDiagram.equiv Q b (piZeroLabel Q b _) = _
  rw [piZeroLabel_unit]
  rfl

lemma piZeroEquiv_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c) (z : SSet.π₀ (functor.obj b)) :
    piZeroEquiv Q hcof hfib c (SSet.mapπ₀ (functor.map f) z) =
      Q.map f.1.unop ≫ piZeroEquiv Q hcof hfib b z ≫ Q.map f.2 := by
  change LocalizedHomDiagram.equiv Q c (piZeroLabel Q c _) = _
  rw [piZeroLabel_base, LocalizedHomDiagram.types_map]
  rfl

include hcof hfib in
lemma map_localized_isIso {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso (AnodyneHomotopy.anodyneQ.map (functor.map f)) := by
  let L := AnodyneHomotopy.anodyneQ.{max u v}
  have : IsIso (L.map (OrdinaryResolutionBar.functor.map f)) :=
    OrdinaryBarBaseInvariance.localized_map_isIso hcof hfib f hs ht
  have (d : Cᵒᵖ × C) : IsIso (L.map (unit.app d)) :=
    Localization.inverts L _ _ (AnodyneKanReplacement.unit_anodyne _)
  have h := congrArg L.map (unit.naturality f)
  rw [L.map_comp, L.map_comp] at h
  have : IsIso (L.map (unit.app b) ≫ L.map (functor.map f)) := h ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

end SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses
