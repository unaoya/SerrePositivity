module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationPostPoints
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 中断した任意モデル源への一般化：PostChoiceFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict small-valued functor for all external postcomposition contexts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0259][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0259
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict small-valued functor for all external postcomposition contexts

The source is the under category of a fixed resolution Y. Equality casts
are part of the transport, so every unit and composite is an actual functor
law, without a functorial choice of source factorizations.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
open SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints

namespace SerrePositivity.HomotopyFunctionComplex.PostChoiceFunctor
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
variable {X Y V W Z : ResolutionObject C} (f : X.base ⟶ Y.base)

omit [ModelCategory SSet.{v}] in
lemma tailTo_compose (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h)
    (c : W ⟶ Z) (k : Y ⟶ Z) (e' : h ≫ c = k) (e'' : g ≫ (b ≫ c) = k) :
    tailTo f g b h e ≫ tailTo f h c k e' = tailTo f g (b ≫ c) k e'' := by
  apply ResolutionLiftSpace.hom_ext
  · have hl := (Category.assoc (tailTo f g b h e) (tailTo f h c k e')
        (ResolutionLiftSpace.inclusion X Z (f ≫ k.base))).trans
      (congrArg (fun q => tailTo f g b h e ≫ q) (tailTo_inclusion f h c k e'))
    have ht := congrArg (fun q => q ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X).obj).map c.diagram)
      (tailTo_inclusion f g b h e)
    have hm := congrArg (fun q => ResolutionLiftSpace.inclusion X V (f ≫ g.base) ≫ q)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X).obj).map_comp b.diagram c.diagram).symm
    exact hl.trans ((Category.assoc _ _ _).symm.trans
      (ht.trans ((Category.assoc _ _ _).trans
        (hm.trans (tailTo_inclusion f g (b ≫ c) k e'').symm))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => tailTo f g b h e ≫ q) (tailTo_projection f h c k e')).trans
        ((tailTo_projection f g b h e).trans (tailTo_projection f g (b ≫ c) k e'').symm))

omit [ModelCategory SSet.{v}] in
lemma tailTo_identity (g : Y ⟶ V) :
    tailTo f g (𝟙 V) g (Category.comp_id g) = 𝟙 _ := by
  apply ResolutionLiftSpace.hom_ext
  · have h := tailTo_inclusion f g (𝟙 V) g (Category.comp_id g)
    change _ = ResolutionLiftSpace.inclusion X V (f ≫ g.base) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X).obj).map (𝟙 V.resolution.obj) at h
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using h
  · exact (tailTo_projection f g (𝟙 V) g (Category.comp_id g)).trans (Category.id_comp _).symm

include hcof in
lemma boundaryTo (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h) :
    postBoundary X Y V f g ≫ tailTo f g b h e = postBoundary X Y W f h := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ ResolutionLiftSpace.baseChange
      (congrArg (fun k => f ≫ k.base) e))
      (CoherentLiftPostComposition.boundary_composite hcof X Y V W f g b)).trans
        (boundary_cast f e))

abbrev transport (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h) :
    postChoiceSpace X Y V f g ⟶ postChoiceSpace X Y W f h :=
  RelativeChoiceSpace.postMap (vertexInclusion X Y f) _ _ (tailTo f g b h e)
    (boundaryTo hcof f g b h e)

lemma transport_existing (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h) :
    transport hcof f g b h e =
      CoherentLiftPostComposition.firstMap hcof X Y V W f g b ≫
        PostCompositionChain.choiceCast f e := by
  rw [choiceCast_postMap, RelativeChoiceSpace.postMap_compose]

lemma transport_identity (g : Y ⟶ V) :
    transport hcof f g (𝟙 V) g (Category.comp_id g) = 𝟙 _ := by
  simp only [transport, tailTo_identity]
  exact RelativeChoiceSpace.postMap_identity _ _

lemma transport_compose (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h)
    (c : W ⟶ Z) (k : Y ⟶ Z) (e' : h ≫ c = k) (e'' : g ≫ (b ≫ c) = k) :
    transport hcof f g b h e ≫ transport hcof f h c k e' =
      transport hcof f g (b ≫ c) k e'' := by
  apply pullback.hom_ext
  · simp only [transport, Category.assoc, RelativeChoiceSpace.postMap_inclusion,
      RelativeChoiceSpace.postMap_inclusion_assoc]
    have hm := congrArg (fun q => (CategoryTheory.ihom
      (CoherentLiftTuples.obj X Y f)).map q) (tailTo_compose f g b h e c k e' e'')
    have hc := ((CategoryTheory.ihom (CoherentLiftTuples.obj X Y f)).map_comp
      (tailTo f g b h e) (tailTo f h c k e')).symm.trans hm
    simpa only [Category.assoc] using congrArg
      (fun q => RelativeChoiceSpace.inclusion (vertexInclusion X Y f)
        (postBoundary X Y V f g) ≫ q) hc
  · simp only [transport, Category.assoc, RelativeChoiceSpace.postMap_projection]

/-- All external postcomposition contexts form one actual small-valued diagram. -/
def functor : Under Y ⥤ SSet.{v} where
  obj g := postChoiceSpace X Y g.right f g.hom
  map {g h} b := transport hcof f g.hom b.right h.hom (Under.w b)
  map_id g := transport_identity hcof f g.hom
  map_comp b c :=
    (transport_compose hcof f _ _ _ (Under.w b) _ _ (Under.w c) (Under.w (b ≫ c))).symm

lemma point_transport (g : Y ⟶ V) (b : V ⟶ W) (h : Y ⟶ W) (e : g ≫ b = h) :
    postLeftPoint hcof X Y V f g ≫ transport hcof f g b h e = postLeftPoint hcof X Y W f h := by
  subst h
  rw [transport_existing]
  change _ ≫ (_ ≫ (𝟙 _)) = _
  rw [Category.comp_id]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _
    (CoherentLiftPostComposition.left_composite hcof X Y V W f g b)

/-- The original left family is a strictly natural point over all postcomposition contexts. -/
def point : (Functor.const (Under Y)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ functor hcof f where
  app g := postLeftPoint hcof X Y g.right f g.hom
  naturality {g h} b := by
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    exact (point_transport hcof f g.hom b.right h.hom (Under.w b)).symm

def projection : functor hcof f ⟶ (Functor.const (Under Y)).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) where
  app g := RelativeChoiceSpace.projection (vertexInclusion X Y f) (postBoundary X Y g.right f g.hom)
  naturality {g h} b := by
    change transport hcof f g.hom b.right h.hom (Under.w b) ≫
      RelativeChoiceSpace.projection (vertexInclusion X Y f) (postBoundary X Y h.right f h.hom) =
        RelativeChoiceSpace.projection (vertexInclusion X Y f)
          (postBoundary X Y g.right f g.hom) ≫ (𝟙 _)
    simp only [transport, RelativeChoiceSpace.postMap_projection, Category.comp_id]

lemma point_projection : point hcof f ≫ projection hcof f = 𝟙 _ := by
  apply NatTrans.ext
  funext g
  exact RelativeChoiceSpace.ofExtension_projection _ _ _
    (postLeft_vertices hcof X Y g.right f g.hom)

lemma projection_trivialFibration
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (g : Under Y) :
    trivialFibrations SSet.{v} ((projection hcof f).app g) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.projection_trivialFibration hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y g.right f g.hom) (ResolutionLiftSpace.projection X g.right (f ≫ g.hom.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X g.right (f ≫ g.hom.base))

lemma point_weakEquivalence
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (g : Under Y) :
    weakEquivalences SSet.{v} ((point hcof f).app g) := by
  have hp := projection_trivialFibration hcof f hfib g
  have he : (point hcof f).app g ≫ (projection hcof f).app g = 𝟙 _ :=
    congr_app (point_projection hcof f) g
  exact (weakEquivalences SSet.{v}).of_postcomp _ _ hp.2
    (he.symm ▸ (weakEquivalences SSet.{v}).id_mem _)

end SerrePositivity.HomotopyFunctionComplex.PostChoiceFunctor
