module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BiresolutionRawMapping

/-!
# 中断した任意モデル源への一般化：BiresolutionRightMapping

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The right-framed double Hom, using the opposite model's actual lift machinery。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0063][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0063
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The right-framed double Hom, using the opposite model's actual lift machinery

The two simplicial directions are exchanged. Opposite arrows identify its
raw diagonal with the ordinary double Hom, before any localization.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.BiresolutionRightMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C]

def sourcePoints : SimplexCategoryᵒᵖ ⥤ (FramedResolution C)ᵒᵖ ⥤ Cᵒᵖ where
  obj n := (FramedResolution.innerDiagrams ⋙ (evaluation SimplexCategory C).obj n.unop).op
  map f :=
    { app X := (X.unop.inner.resolution.obj.map f.unop).op
      naturality {X Y} g := by
        apply Quiver.Hom.unop_inj
        exact g.unop.map.diagram.naturality f.unop }
  map_id n := by
    apply NatTrans.ext
    funext X
    apply Quiver.Hom.unop_inj
    exact X.unop.inner.resolution.obj.map_id n.unop
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Quiver.Hom.unop_inj
    exact X.unop.inner.resolution.obj.map_comp g.unop f.unop

lemma sourcePoint_isFibrant (X : (FramedResolution C)ᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    IsFibrant (((sourcePoints (C := C)).obj n).obj X) := by
  have : IsCofibrant (X.unop.inner.resolution.obj.obj n.unop) :=
    X.unop.inner.resolution.isCofibrant_obj n.unop
  exact (isFibrant_iff_of_isTerminal (initial.to (X.unop.inner.resolution.obj.obj n.unop)).op
    (terminalOpOfInitial initialIsInitial)).mpr inferInstance

def presentationRows : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤
    Cᵒᵖ × (FramedResolution Cᵒᵖ)ᵒᵖ where
  obj n := (sourcePoints.obj n).prod (𝟭 _)
  map f := NatTrans.prod (sourcePoints.map f) (𝟙 _)
  map_id _ := by
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · exact congr_app (sourcePoints.map_id _) X.1
    · rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · exact congr_app (sourcePoints.map_comp f g) X.1
    · exact (Category.id_comp _).symm

abbrev rawUncurried : Cᵒᵖ × (FramedResolution Cᵒᵖ)ᵒᵖ ⥤ SSet.{v} :=
  Functor.uncurry.obj (FramedResolution.raw (C := Cᵒᵖ)).flip

abbrev rawRows : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤ SSet.{v} :=
  presentationRows ⋙ (Functor.whiskeringRight (RightResolutionMapping.Index C)
    (Cᵒᵖ × (FramedResolution Cᵒᵖ)ᵒᵖ) SSet.{v}).obj rawUncurried

abbrev rawFunctor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  (rawRows (C := C)).flip ⋙ BisimplicialModel.diagonal

lemma raw_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : RightResolutionMapping.Index C) :
    (rawRows.map θ).app X = ((FramedResolution.raw (C := Cᵒᵖ)).obj X.2).map
      ((sourcePoints.map θ).app X.1) := by
  change _ ≫ ((FramedResolution.raw (C := Cᵒᵖ)).map (𝟙 X.2)).app _ = _
  rw [(FramedResolution.raw (C := Cᵒᵖ)).map_id]
  exact Category.comp_id _

def rawSimplexEquiv (X : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    ((BiresolutionRawMapping.functor (C := C)).obj X).obj n ≃
      ((rawFunctor (C := C)).obj X).obj n where
  toFun f := f.op
  invFun f := f.unop
  left_inv _ := rfl
  right_inv _ := rfl

def rawFlipComponent (X : RightResolutionMapping.Index C) :
    (BiresolutionRawMapping.functor (C := C)).obj X ≅ (rawFunctor (C := C)).obj X :=
  NatIso.ofComponents (fun n => Equiv.toIso (rawSimplexEquiv X n)) (by
    intro n m f
    ext h
    apply (Quiver.Hom.unop_inj (C := C))
    dsimp [rawSimplexEquiv, RightResolutionMapping.presentationRows,
      DualResolutionTargets.framedPresentation, DualResolutionTargets.framedForget,
      DualResolutionTargets.presentations, DualResolutionTargets.presentation,
      DualResolutionTargets.diagram, presentationRows, sourcePoints,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom,
      FramedResolution.innerDiagrams, FramedResolution.forget, ResolutionObject.diagrams,
      ResolutionObject.instCategory,
      SerrePositivity.ModelReplacement.FibrantReplacementObject.targets, Equiv.toIso]
    simp only [Category.assoc]
    change X.1.unop.inner.resolution.obj.map f.unop ≫ 𝟙 _ ≫ h ≫
        (X.2.unop.inner.resolution.obj.map f.unop).unop =
      X.1.unop.inner.resolution.obj.map f.unop ≫ h ≫ 𝟙 _ ≫
        (X.2.unop.inner.resolution.obj.map f.unop).unop
    simp only [Category.id_comp])


/-- This exchanges the two actual Hom coordinates by taking opposite arrows. -/
def rawFlipIso : BiresolutionRawMapping.functor (C := C) ≅ rawFunctor :=
  NatIso.ofComponents rawFlipComponent (by
    intro X Y f
    ext n h
    apply (Quiver.Hom.unop_inj (C := C))
    dsimp [rawFlipComponent, rawSimplexEquiv, RightResolutionMapping.presentationRows,
      DualResolutionTargets.framedPresentation, DualResolutionTargets.framedForget,
      DualResolutionTargets.presentations, DualResolutionTargets.presentation,
      DualResolutionTargets.diagram, presentationRows, sourcePoints,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom,
      FramedResolution.innerDiagrams, FramedResolution.forget, ResolutionObject.diagrams,
      ResolutionObject.instCategory,
      SerrePositivity.ModelReplacement.FibrantReplacementObject.targets, Equiv.toIso]
    )

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev homUncurried : Cᵒᵖ × (FramedResolution Cᵒᵖ)ᵒᵖ ⥤ SSet.{v} :=
  Functor.uncurry.obj (FramedResolution.hom (C := Cᵒᵖ) hcof hfib).flip

abbrev rows : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤ SSet.{v} :=
  presentationRows ⋙ (Functor.whiskeringRight (RightResolutionMapping.Index C)
    (Cᵒᵖ × (FramedResolution Cᵒᵖ)ᵒᵖ) SSet.{v}).obj (homUncurried hcof hfib)

abbrev functor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  (rows hcof hfib).flip ⋙ BisimplicialModel.diagonal

lemma hom_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : RightResolutionMapping.Index C) :
    ((rows hcof hfib).map θ).app X =
      ((FramedResolution.hom (C := Cᵒᵖ) hcof hfib).obj X.2).map
        ((sourcePoints.map θ).app X.1) := by
  change _ ≫ ((FramedResolution.hom (C := Cᵒᵖ) hcof hfib).map (𝟙 X.2)).app _ = _
  rw [(FramedResolution.hom (C := Cᵒᵖ) hcof hfib).map_id]
  exact Category.comp_id _

abbrev uncurriedComparison : rawUncurried (C := C) ⟶ homUncurried hcof hfib :=
  Functor.uncurry.map
    ((CategoryTheory.flipFunctor (FramedResolution Cᵒᵖ)ᵒᵖ Cᵒᵖ SSet.{v}).map
      (FramedResolution.comparison hcof hfib))

def rowsComparison : rawRows (C := C) ⟶ rows hcof hfib where
  app n := Functor.whiskerLeft (presentationRows.obj n) (uncurriedComparison hcof hfib)
  naturality {n m} f := by
    apply NatTrans.ext
    funext X
    exact (uncurriedComparison hcof hfib).naturality ((presentationRows.map f).app X)

def comparison : rawFunctor (C := C) ⟶ functor hcof hfib :=
  Functor.whiskerRight
    ((CategoryTheory.flipFunctor SimplexCategoryᵒᵖ (RightResolutionMapping.Index C) SSet.{v}).map
      (rowsComparison hcof hfib)) BisimplicialModel.diagonal

lemma comparison_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((comparison hcof hfib).app X) := by
  apply BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
  intro n
  have := sourcePoint_isFibrant X.1 n
  exact FramedResolution.comparison_weakEquivalence hcof hfib X.2
    (((sourcePoints (C := C)).obj n).obj X.1)

end SerrePositivity.HomotopyFunctionComplex.BiresolutionRightMapping
