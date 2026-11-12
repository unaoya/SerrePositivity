module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization

/-!
# 実際の frame 実現随伴の係数自然性

概要：Hovey §5 の実際の Yoneda 拡張の Hom 随伴は frame の射に自然。
方針：随伴の各単体の式と同じ Kan 拡張の単位の自然性を使う。
規約：実現の射は既存の Realization.family の同じ射。
使われ方：各値の重み付き始域 Hom と図式 frame Hom の自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory Limits
open SerrePositivity.HomotopyFunctionComplex

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {A B : SimplexCategory ⥤ C}

/-- 概要：実際の実現随伴の単体の像は単位と代表射の合成（Hovey §5）。
方針：ulift Yoneda 随伴の同じ計算式から内部の ULift を消す。
規約：元の単体と元の実現対象を保持する。
使われ方：係数 frame の射の自然性の成分計算。 -/
lemma realizationHomEquiv_app {X : SSet.{u}} {Y : C}
    (f : (Realization.functor A).obj X ⟶ Y) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (((Realization.adjunction A).homEquiv X Y f).app n) x =
      (Realization.unit A).app n.unop ≫
        (Realization.functor A).map (uliftYonedaEquiv.symm x) ≫ f := by
  change ((((Presheaf.uliftYonedaAdjunction.{0, 0, u} (Realization.functor A)
    (Realization.unit A)).homEquiv X Y f).app n) x).down = _
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]

/-- 概要：frame 実現の Hom 随伴は元の係数射に自然（Hovey §5）。
方針：各単体で単位の自然性と実現族の自然性を合成する。
規約：既存の Kan 拡張関手の同じ係数射を使う。
使われ方：図式の frame Hom 比較の始域自然性。 -/
lemma realizationHomEquiv_source (a : A ⟶ B) (X : SSet.{u}) (Y : C)
    (f : (Realization.functor B).obj X ⟶ Y) :
    (Realization.adjunction A).homEquiv X Y ((Realization.family.map a).app X ≫ f) =
      (Realization.adjunction B).homEquiv X Y f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app Y := by
  ext n x
  change (((Realization.adjunction A).homEquiv X Y (_ ≫ f)).app n) x =
    a.app n.unop ≫ (((Realization.adjunction B).homEquiv X Y f).app n) x
  rw [realizationHomEquiv_app, realizationHomEquiv_app]
  have hu := congr_app (Realization.unit_naturality a) n.unop
  have hn := (Realization.family.map a).naturality (uliftYonedaEquiv.symm x)
  change a.app n.unop ≫ (Realization.unit B).app n.unop =
    (Realization.unit A).app n.unop ≫ (Realization.family.map a).app
      (uliftYoneda.obj n.unop) at hu
  change (Realization.functor A).map (uliftYonedaEquiv.symm x) ≫
      (Realization.family.map a).app X =
    (Realization.family.map a).app (uliftYoneda.obj n.unop) ≫
      (Realization.functor B).map (uliftYonedaEquiv.symm x) at hn
  rw [← Category.assoc (a.app _), hu]
  simp only [Category.assoc]
  rw [← Category.assoc _ ((Realization.family.map a).app X), hn, Category.assoc]

end SerrePositivity.EInfinity.FrameHom
