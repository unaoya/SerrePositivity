module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpace
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne

/-!
# 中断した任意モデル源への一般化：ResolutionLiftSpace

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Higher compatibility spaces for arbitrary resolution lifts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0311][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0311
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Higher compatibility spaces for arbitrary resolution lifts

A second cosimplicial resolution in the actual Reedy model gives a derived
space of lifts over each base map. Every strict resolution lift supplies an
actual point. All monomorphic boundary data extend; no functorial source
factorization is assumed. These spaces do not yet define a strict action
or composition of mapping spaces.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionLiftSpace
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C

abbrev frame (X : ResolutionObject C) :
    CofibrantResolution simplex X.resolution.obj := cosimplicialResolution X.resolution.obj

abbrev baseMap (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    X.resolution.obj ⟶ (Functor.const SimplexCategory).obj Y.base :=
  X.resolution.augmentation ≫ (Functor.const SimplexCategory).map f

/-- A derived simplicial space of lifts of f between the two resolutions. -/
abbrev obj (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : SSet.{v} :=
  LiftSpace.obj (frame X).obj (frame X).augmentation
    Y.resolution.augmentation (baseMap X Y f)

abbrev projection (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    obj X Y f ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) :=
  LiftSpace.projection (frame X).obj (frame X).augmentation
    Y.resolution.augmentation (baseMap X Y f)

/-- Embed any actual resolution lift into this space of compatible choices. -/
def ofLift {X Y : ResolutionObject C} (f : X ⟶ Y) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj X Y f.base :=
  LiftSpace.ofLift (frame X).obj (frame X).augmentation
    Y.resolution.augmentation (baseMap X Y f.base) f.diagram f.over

local instance augmentation_fibration (Y : ResolutionObject C) :
    Fibration Y.resolution.augmentation := ⟨fun n => (Y.resolution.trivial n).1⟩
local instance augmentation_weakEquivalence (Y : ResolutionObject C) :
    WeakEquivalence Y.resolution.augmentation := ⟨Y.resolution.augmentation_weakEquivalence⟩

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma projection_trivialFibration (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    trivialFibrations SSet.{v} (projection X Y f) :=
  LiftSpace.projection_trivialFibration _ _ hcof (frame X).cofibrant _ _

include hcof in
/-- Compatibility already prescribed on any simplicial subcomplex extends. -/
lemma extension (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (g : K ⟶ obj X Y f) :
    ∃ e : L ⟶ obj X Y f, i ≫ e = g :=
  LiftSpace.extension _ _ hcof (frame X).cofibrant _ _ i g

include hcof in
/-- Any two strict lift choices are joined by an actual simplicial interval. -/
lemma interval (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    (s t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj X Y f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj X Y f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = s ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = t := by
  let b := BoundaryOne.isColimit.desc (BinaryCofan.mk s t)
  obtain ⟨e, he⟩ := extension hcof X Y f (SSet.boundary 1).ι b
  refine ⟨e, ?_, ?_⟩
  · change SSet.stdSimplex.δ (1 : Fin 2) ≫ e = s
    rw [← SSet.boundary.ι_ι (1 : Fin 2), Category.assoc, he]
    exact BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.left⟩
  · change SSet.stdSimplex.δ (0 : Fin 2) ≫ e = t
    rw [← SSet.boundary.ι_ι (0 : Fin 2), Category.assoc, he]
    exact BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.right⟩

include hcof in
lemma kanComplex (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    SSet.KanComplex (obj X Y f) :=
  LiftSpace.kanComplex _ _ hcof (frame X).cofibrant hfib _ _

/-- Contractibility in any chosen ordinary homotopy category of spaces. -/
def localizationIso (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {H : Type*} [Category* H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})]
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    L.obj (obj X Y f) ≅ L.obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) :=
  LiftSpace.localizationIso _ _ hcof (frame X).cofibrant L _ _

end SerrePositivity.HomotopyFunctionComplex.ResolutionLiftSpace
