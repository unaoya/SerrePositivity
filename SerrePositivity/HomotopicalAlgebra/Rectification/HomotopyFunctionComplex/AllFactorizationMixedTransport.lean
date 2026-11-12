module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationPre

/-!
# 中断した任意モデル源への一般化：AllFactorizationMixedTransport

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict transport of the global source comparison through target composition。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0052][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0052
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict transport of the global source comparison through target composition

The same fixed-boundary space receives both orders of external change.
The transport squares are equations of actual simplicial maps.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedTransport
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {X' X Y V W : ResolutionObject C} (a : X' ⟶ X) (f : X.base ⟶ Y.base)
  (g : Y ⟶ V) (b : V ⟶ W) (φ : ResolutionLiftPrecomposition.FrameMap a)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev tail : ResolutionLiftSpace.obj X' V (a.base ≫ f ≫ g.base) ⟶
    ResolutionLiftSpace.obj X' W (a.base ≫ f ≫ (g ≫ b).base) :=
  ResolutionLiftPostcomposition.map X' V W (a.base ≫ f ≫ g.base) b ≫
    ResolutionLiftSpace.baseChange (by
      change (a.base ≫ f ≫ g.base) ≫ b.base = a.base ≫ f ≫ (g.base ≫ b.base)
      simp only [Category.assoc])

omit [ModelCategory SSet.{v}] in
@[reassoc]
lemma tail_inclusion : tail a f g b ≫
    ResolutionLiftSpace.inclusion X' W (a.base ≫ f ≫ (g ≫ b).base) =
    ResolutionLiftSpace.inclusion X' V (a.base ≫ f ≫ g.base) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X').obj).map b.diagram := by
  change (_ ≫ ResolutionLiftSpace.baseChange _) ≫ _ = _
  rw [Category.assoc, ResolutionLiftSpace.baseChange_inclusion,
    ResolutionLiftSpace.post_inclusion]

omit [ModelCategory SSet.{v}] in
@[reassoc]
lemma tail_projection : tail a f g b ≫
    ResolutionLiftSpace.projection X' W (a.base ≫ f ≫ (g ≫ b).base) =
    ResolutionLiftSpace.projection X' V (a.base ≫ f ≫ g.base) := by
  change (_ ≫ ResolutionLiftSpace.baseChange _) ≫ _ = _
  rw [Category.assoc, ResolutionLiftSpace.baseChange_projection,
    ResolutionLiftPostcomposition.map_projection]

omit [ModelCategory SSet.{v}] in
@[reassoc]
lemma postTail_inclusion (S : ResolutionObject C) (h : S.base ⟶ Y.base) :
    CoherentLiftPostComposition.tailMap S Y V W h g b ≫
      ResolutionLiftSpace.inclusion S W (h ≫ (g ≫ b).base) =
    ResolutionLiftSpace.inclusion S V (h ≫ g.base) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame S).obj).map b.diagram := by
  change (ResolutionLiftPostcomposition.map S V W (h ≫ g.base) b ≫
    ResolutionLiftSpace.baseChange (Category.assoc h g.base b.base)) ≫
      ResolutionLiftSpace.inclusion S W (h ≫ g.base ≫ b.base) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => ResolutionLiftPostcomposition.map S V W (h ≫ g.base) b ≫ q)
      (ResolutionLiftSpace.baseChange_inclusion (Category.assoc h g.base b.base))).trans
        (ResolutionLiftSpace.post_inclusion S V W (h ≫ g.base) b))

omit [ModelCategory SSet.{v}] in
@[reassoc]
lemma postTail_projection (S : ResolutionObject C) (h : S.base ⟶ Y.base) :
    CoherentLiftPostComposition.tailMap S Y V W h g b ≫
      ResolutionLiftSpace.projection S W (h ≫ (g ≫ b).base) =
    ResolutionLiftSpace.projection S V (h ≫ g.base) := by
  change (ResolutionLiftPostcomposition.map S V W (h ≫ g.base) b ≫
    ResolutionLiftSpace.baseChange (Category.assoc h g.base b.base)) ≫
      ResolutionLiftSpace.projection S W (h ≫ g.base ≫ b.base) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => ResolutionLiftPostcomposition.map S V W (h ≫ g.base) b ≫ q)
      (ResolutionLiftSpace.baseChange_projection (Category.assoc h g.base b.base))).trans
        (ResolutionLiftPostcomposition.map_projection S V W (h ≫ g.base) b))

omit [ModelCategory SSet.{v}] in
lemma pre_tail : CoherentLiftMixedComparison.preTail X' X Y V a f g φ ≫ tail a f g b =
    CoherentLiftPostComposition.tailMap X Y V W f g b ≫
      CoherentLiftMixedComparison.preTail X' X Y W a f (g ≫ b) φ := by
  apply ResolutionLiftSpace.hom_ext
  · rw [Category.assoc, tail_inclusion, ← Category.assoc, ResolutionLiftSpace.pre_inclusion,
      Category.assoc, Category.assoc, ResolutionLiftSpace.pre_inclusion]
    have hp := congrArg (fun q => q ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ.val).app W.resolution.obj)
      (postTail_inclusion g b X f)
    have hn := congrArg (fun k => ResolutionLiftSpace.inclusion X V (f ≫ g.base) ≫ k)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap φ.val).naturality b.diagram).symm
    exact hn.trans (by simpa only [Category.assoc] using hp.symm)
  · rw [Category.assoc, tail_projection, ResolutionLiftSpace.pre_projection,
      Category.assoc, ResolutionLiftSpace.pre_projection, postTail_projection]

omit [ModelCategory SSet.{v}] in
lemma cast_tail : CoherentLiftMixedComparison.castMap X' X Y V a f g ≫ tail a f g b =
    CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b ≫
      CoherentLiftMixedComparison.castMap X' X Y W a f (g ≫ b) := by
  apply ResolutionLiftSpace.hom_ext
  · have hl := (Category.assoc
        (CoherentLiftMixedComparison.castMap X' X Y V a f g) (tail a f g b)
        (ResolutionLiftSpace.inclusion X' W (a.base ≫ f ≫ (g ≫ b).base))).trans
        (congrArg (fun q => CoherentLiftMixedComparison.castMap X' X Y V a f g ≫ q)
          (tail_inclusion a f g b))
    have hc := congrArg (fun q => q ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X').obj).map b.diagram)
      (ResolutionLiftSpace.baseChange_inclusion (Category.assoc a.base f g.base))
    have hr := (Category.assoc
        (CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b)
        (CoherentLiftMixedComparison.castMap X' X Y W a f (g ≫ b))
        (ResolutionLiftSpace.inclusion X' W (a.base ≫ f ≫ (g ≫ b).base))).trans
      (congrArg (fun q => CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b ≫ q)
        (ResolutionLiftSpace.baseChange_inclusion (Category.assoc a.base f (g ≫ b).base)))
    have hc' : CoherentLiftMixedComparison.castMap X' X Y V a f g ≫
        (ResolutionLiftSpace.inclusion X' V (a.base ≫ f ≫ g.base) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X').obj).map b.diagram) =
        ResolutionLiftSpace.inclusion X' V ((a.base ≫ f) ≫ g.base) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame X').obj).map b.diagram := by
      simpa only [Category.assoc] using hc
    exact hl.trans (hc'.trans ((postTail_inclusion g b X' (a.base ≫ f)).symm.trans hr.symm))
  · have hl := (Category.assoc
        (CoherentLiftMixedComparison.castMap X' X Y V a f g) (tail a f g b)
        (ResolutionLiftSpace.projection X' W (a.base ≫ f ≫ (g ≫ b).base))).trans
        ((congrArg (fun q => CoherentLiftMixedComparison.castMap X' X Y V a f g ≫ q)
          (tail_projection a f g b)).trans
          (ResolutionLiftSpace.baseChange_projection (Category.assoc a.base f g.base)))
    have hr := (Category.assoc
        (CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b)
        (CoherentLiftMixedComparison.castMap X' X Y W a f (g ≫ b))
        (ResolutionLiftSpace.projection X' W (a.base ≫ f ≫ (g ≫ b).base))).trans
      ((congrArg (fun q => CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b ≫ q)
        (ResolutionLiftSpace.baseChange_projection (Category.assoc a.base f (g ≫ b).base))).trans
          (postTail_projection g b X' (a.base ≫ f)))
    exact hl.trans hr.symm

include hcof in
lemma boundary_tail : CoherentLiftMixedComparison.boundary X' X Y V a f g φ ≫ tail a f g b =
    CoherentLiftMixedComparison.boundary X' X Y W a f (g ≫ b) φ := by
  change (_ ≫ _) ≫ _ = _ ≫ _
  calc
    _ = postBoundary X Y V f g ≫
        (CoherentLiftMixedComparison.preTail X' X Y V a f g φ ≫ tail a f g b) :=
      Category.assoc _ _ _
    _ = postBoundary X Y V f g ≫
        (CoherentLiftPostComposition.tailMap X Y V W f g b ≫
          CoherentLiftMixedComparison.preTail X' X Y W a f (g ≫ b) φ) :=
      congrArg (fun k => postBoundary X Y V f g ≫ k) (pre_tail a f g b φ)
    _ = (postBoundary X Y V f g ≫ CoherentLiftPostComposition.tailMap X Y V W f g b) ≫
        CoherentLiftMixedComparison.preTail X' X Y W a f (g ≫ b) φ :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ CoherentLiftMixedComparison.preTail X' X Y W a f (g ≫ b) φ)
      (CoherentLiftPostComposition.boundary_composite hcof X Y V W f g b)

abbrev choiceMap : AllFactorizationPre.choiceSpace a f g φ ⟶
    AllFactorizationPre.choiceSpace a f (g ≫ b) φ :=
  RelativeChoiceSpace.postMap (vertexInclusion X Y f) _ _ (tail a f g b)
    (boundary_tail hcof a f g b φ)

lemma mapAC_tail : CoherentLiftMixedComparison.mapAC X' X Y V a f g φ ≫
    choiceMap hcof a f g b φ =
    CoherentLiftPostComposition.firstMap hcof X Y V W f g b ≫
      CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ := by
  apply pullback.hom_ext
  · simp only [choiceMap, CoherentLiftMixedComparison.mapAC,
      CoherentLiftPostComposition.firstMap, Category.assoc,
      RelativeChoiceSpace.postMap_inclusion, RelativeChoiceSpace.postMap_inclusion_assoc]
    rw [← CategoryTheory.Functor.map_comp, pre_tail, CategoryTheory.Functor.map_comp]
  · simp only [choiceMap, CoherentLiftMixedComparison.mapAC,
      CoherentLiftPostComposition.firstMap, Category.assoc, RelativeChoiceSpace.postMap_projection]

lemma mapBD_tail : CoherentLiftMixedComparison.mapBD hcof X' X Y V a f g φ ≫
    choiceMap hcof a f g b φ =
    CoherentLiftPostComposition.firstMap hcof X' Y V W (a.base ≫ f) g b ≫
      CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ := by
  apply pullback.hom_ext
  · simp only [choiceMap, CoherentLiftMixedComparison.mapBD,
      CoherentLiftPostComposition.firstMap, Category.assoc,
      RelativeChoiceSpace.postMap_inclusion, RelativeChoiceSpace.preMap_inclusion,
      RelativeChoiceSpace.postMap_inclusion_assoc, RelativeChoiceSpace.preMap_inclusion_assoc]
    have hn := (CategoryTheory.MonoidalClosed.internalHom.map
      (CoherentLiftMixedComparison.tuplePre X' X Y a f).op).naturality (tail a f g b)
    apply congrArg (fun q => RelativeChoiceSpace.inclusion (vertexInclusion X' Y (a.base ≫ f))
      (postBoundary X' Y V (a.base ≫ f) g) ≫ q)
    calc
      _ = (ihom (CoherentLiftTuples.obj X' Y (a.base ≫ f))).map
          (CoherentLiftMixedComparison.castMap X' X Y V a f g) ≫
          ((ihom (CoherentLiftTuples.obj X' Y (a.base ≫ f))).map (tail a f g b) ≫
            (CategoryTheory.MonoidalClosed.internalHom.map
              (CoherentLiftMixedComparison.tuplePre X' X Y a f).op).app _) :=
        congrArg (fun q => (ihom (CoherentLiftTuples.obj X' Y (a.base ≫ f))).map
          (CoherentLiftMixedComparison.castMap X' X Y V a f g) ≫ q) hn.symm
      _ = _ := by
        let F := ihom (CoherentLiftTuples.obj X' Y (a.base ≫ f))
        have hm := (F.map_comp (CoherentLiftMixedComparison.castMap X' X Y V a f g)
          (tail a f g b)).symm.trans
          ((congrArg F.map (cast_tail a f g b)).trans
            (F.map_comp (CoherentLiftPostComposition.tailMap X' Y V W (a.base ≫ f) g b)
              (CoherentLiftMixedComparison.castMap X' X Y W a f (g ≫ b))))
        simpa only [Category.assoc] using congrArg (fun q => q ≫
          (CategoryTheory.MonoidalClosed.internalHom.map
            (CoherentLiftMixedComparison.tuplePre X' X Y a f).op).app
              (ResolutionLiftSpace.obj X' W (a.base ≫ f ≫ (g ≫ b).base))) hm
  · simp only [choiceMap, CoherentLiftMixedComparison.mapBD,
      CoherentLiftPostComposition.firstMap, Category.assoc,
      RelativeChoiceSpace.postMap_projection, RelativeChoiceSpace.preMap_projection]

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedTransport
