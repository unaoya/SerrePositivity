module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameDiagrams

/-!
# 混合 Hom の始域 frame に関する自然な前合成

概要：Hovey §5.4 の混合 Hom の共同比較を始域 frame の射に自然にする。
方針：cosimplicial Hom と元の Hom の前合成を同じ対角へ移す。
規約：元の frame の射と augmentation の可換四角形を保持する。
使われ方：具体的な両錐比較の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.FrameHom.MixedFrame

open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] {A B : SimplexCategory ⥤ C}

/-- 概要：混合 Hom は始域 frame に反変（Hovey §5）。
方針：始域 frame の Hom の前合成を終域図式と対角へ後合成する。
規約：各次元で元の frame 射を前合成する。
使われ方：両 frame 比較の共通図式の始域の射。 -/
abbrev mixedSourceMap (a : A ⟶ B) : mixedFunctor B ⟶ mixedFunctor A :=
  Functor.whiskerRight
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ C SSet.{v}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a))
    SerrePositivity.BisimplicialModel.diagonal

/-- 概要：右 Hom は元の始域の射に反変（Hovey §5）。
方針：元の Hom の前合成を終域の単体図式へ後合成する。
規約：始域の置換や比較射を追加しない。
使われ方：右 frame の錐の始域の射。 -/
abbrev rightSourceMap {X Y : C} (f : X ⟶ Y) : rightHomFunctor Y ⟶ rightHomFunctor X :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ C (Type v)).map (coyoneda.map f.op)

variable (K : Type v) [SmallCategory K]

/-- 概要：混合 Hom への左比較は始域 frame の前合成に自然（Hovey §5.4）。
方針：元の射の前合成と後合成の結合則を各値で使う。
規約：終域の augmentation は同じものを使う。
使われ方：両錐比較の左側の可換四角形。 -/
lemma leftDiagramComparison_source (a : A ⟶ B) (F : K ⥤ C)
    (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C) (b : F ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ R) :
    Functor.whiskerLeft F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a) ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K A F R b =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K B F R b ≫ Functor.whiskerLeft R (mixedSourceMap a) := by
  ext k n h
  change (a.app n.unop ≫ h) ≫ (b.app k).app n =
    a.app n.unop ≫ (h ≫ (b.app k).app n)
  exact Category.assoc _ _ _

/-- 概要：混合 Hom への右比較は augmentation の可換四角形に自然（Hovey §5.4）。
方針：同じ四角形の各成分を元の右 Hom の前合成へ移す。
規約：frame の射と元の始域の射を同時に指定する。
使われ方：両錐比較の右側の可換四角形。 -/
lemma rightDiagramComparison_source {X Y : C} (a : A ⟶ B) (f : X ⟶ Y)
    (p : A ⟶ (Functor.const SimplexCategory).obj X)
    (q : B ⟶ (Functor.const SimplexCategory).obj Y)
    (h : a ≫ q = p ≫ (Functor.const SimplexCategory).map f)
    (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C) :
    Functor.whiskerLeft R (rightSourceMap f) ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K A p R =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K B q R ≫ Functor.whiskerLeft R (mixedSourceMap a) := by
  ext k n g
  change p.app n.unop ≫ (f ≫ g) = a.app n.unop ≫ (q.app n.unop ≫ g)
  have hn : a.app n.unop ≫ q.app n.unop = p.app n.unop ≫ f := congr_app h n.unop
  rw [← Category.assoc, ← hn, Category.assoc]

end SerrePositivity.EInfinity.FrameHom.MixedFrame
