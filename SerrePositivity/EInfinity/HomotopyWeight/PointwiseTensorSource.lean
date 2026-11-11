module

public import SerrePositivity.EInfinity.HomotopyWeight.PointwiseTensorFrame
public import SerrePositivity.EInfinity.FrameHom.RealizationHomNaturality

/-!
# 各値で実現した図式 frame の Hom 同型の係数自然性

概要：Hovey §5.4 の図式 frame Hom と重み付き始域 Hom の同型は係数に自然。
方針：同じ各値の実現随伴の自然性を重みのテンソル随伴と合成する。
規約：実現の射は元の Yoneda 拡張族の同じ射。
使われ方：元の定値図式からの局所化 Hom の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {B B' : SimplexCategory ⥤ C} (a : B ⟶ B')

/-- 概要：各値の実現随伴は同じ frame 射に自然（Hovey §5）。
方針：図式の各値で元の実現随伴の自然性を使う。
規約：図式のすべての単体を同時に比較する。
使われ方：テンソル実現の合成随伴の係数自然性。 -/
lemma pointwiseRealization_homEquiv_source (X : K ⥤ SSet.{u}) (F : K ⥤ C)
    (f : (pointwiseRealization K B').obj X ⟶ F) :
    (pointwiseRealizationAdjunction K B).homEquiv X F
        (((Functor.whiskeringRight K SSet.{u} C).map (Realization.family.map a)).app X ≫ f) =
      (pointwiseRealizationAdjunction K B').homEquiv X F f ≫
        ((Functor.whiskeringRight K C SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)).app F := by
  ext k n x
  change (((Realization.adjunction B).homEquiv (X.obj k) (F.obj k)
      ((Realization.family.map a).app (X.obj k) ≫ f.app k)).app n) x =
    a.app n.unop ≫ (((Realization.adjunction B').homEquiv (X.obj k) (F.obj k)
      (f.app k)).app n) x
  exact congrArg (fun g => (g.app n) x)
    (FrameHom.realizationHomEquiv_source a (X.obj k) (F.obj k) (f.app k))

variable (W : K ⥤ SSet.{u})

/-- 概要：各値のテンソル実現随伴は係数 frame に自然（Hovey §5.4）。
方針：各値の実現随伴の自然性と重みの錐随伴の終域自然性を使う。
規約：元の射影重みを変更しない。
使われ方：図式の標準 frame の Hom 同型の自然性。 -/
lemma pointwiseTensorAdjunction_source (X : SSet.{u}) (F : K ⥤ C)
    (f : (pointwiseTensorRealization K W B').obj X ⟶ F) :
    (pointwiseTensorAdjunction K W B).homEquiv X F
        (((Functor.whiskeringRight K SSet.{u} C).map (Realization.family.map a)).app
          ((WeightedCones.tensorDiagram K W).obj X) ≫ f) =
      (pointwiseTensorAdjunction K W B').homEquiv X F f ≫
        (WeightedCones.coneSpace K W).map
          (((Functor.whiskeringRight K C SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)).app F) := by
  simp only [pointwiseTensorAdjunction, Adjunction.comp_homEquiv]
  have hn := pointwiseRealization_homEquiv_source K a
    ((WeightedCones.tensorDiagram K W).obj X) F f
  exact (congrArg ((WeightedCones.adjunction K W).homEquiv X
    ((pointwiseFrameHom K B).obj F)) hn).trans
      ((WeightedCones.adjunction K W).homEquiv_naturality_right _ _)

/-- 概要：図式 frame の Hom 同型は元の係数射に自然（Hovey §5.4）。
方針：標準単体ごとに合成随伴の自然性を Yoneda 同型へ移す。
規約：全次元で同じ実現族の射を使う。
使われ方：定値図式の π₀ の Hom 比較の始域自然性。 -/
lemma pointwiseTensorFrameHomIso_source (F : K ⥤ C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerLeft
        (SSet.stdSimplex ⋙ WeightedCones.tensorDiagram K W)
        ((Functor.whiskeringRight K SSet.{u} C).map (Realization.family.map a)))).app F ≫
          (pointwiseTensorFrameHomIso K W B).hom.app F =
      (pointwiseTensorFrameHomIso K W B').hom.app F ≫ (WeightedCones.coneSpace K W).map
        (((Functor.whiskeringRight K C SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)).app F) := by
  ext n f
  change SSet.yonedaEquiv ((pointwiseTensorAdjunction K W B).homEquiv _ F (_ ≫ f)) =
    (((WeightedCones.coneSpace K W).map
      (((Functor.whiskeringRight K C SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)).app F)).app n)
        (SSet.yonedaEquiv ((pointwiseTensorAdjunction K W B').homEquiv _ F f))
  rw [← SSet.yonedaEquiv_comp]
  exact congrArg SSet.yonedaEquiv (pointwiseTensorAdjunction_source K a W _ F f)

end SerrePositivity.EInfinity.HomotopyWeight
