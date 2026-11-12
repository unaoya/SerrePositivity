module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHomInfinity
public import SerrePositivity.EInfinity.FrameHom.AsSmallHammockHomNormalization
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockYonedaNormalization
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelRightFrameComparison

/-!
概要：同じ全 Hom 比較の合成と指定二胞体による元の局所化辺の回収。
方針：実終端・同じ原本 Yoneda・同じ K 輸送を露出し、元の三角形の自然性を使う。
規約：全同型とは別の局所化比較や二胞体を選び直さない。
使われ方：Sp が全図式比較と元の辺の零単体の正規化を同時に合成する入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SerrePositivity.EInfinity.SimplicialLocalization
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  {G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q}
  (c : CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G)

/-- 概要：全同型の順射は同じ実終端・原本 Yoneda・指定輸送の順の合成。
方針：元の主定義の合成を露出する。
規約：全関手圏の射の等式。使われ方：零単体を同じ全比較の中で追跡する。 -/
lemma rightFrameTerminalHomIso_hom :
    (rightFrameTerminalHomIso q r c).hom =
      (rightFrameHammockTerminalRealizationIso q r).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
          (kanHammockHomInfinityIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
          (SSet.uliftFunctor.{max u v + 1, max u v}.map
            (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))).hom ≫
        (c.homInfinityTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))).hom := rfl

/-- 概要：同じ全図式同型と同じ比較二胞体を一緒に公開する。
方針：主比較と元の指定データを組にする。
規約：比較 K と二胞体を保存。使われ方：消費者の coherent な合成。 -/
def rightFrameTerminalHomComparison := (rightFrameTerminalHomIso q r c, c)

/-- 概要：同じ全比較の指定二胞体は入力した二胞体そのもの。
方針：組の第二成分を評価する。
規約：厳密な等式。使われ方：元の局所化辺の共役式との接続。 -/
lemma rightFrameTerminalHomComparison_triangle :
    (rightFrameTerminalHomComparison q r c).2.triangle = c.triangle := rfl

/-- 概要：同じ全比較に保持した二胞体の両端で元の局所化射を回収する。
方針：指定された元の二胞体の自然性による既存の共役公式を使う。
規約：生の辺の厳密化を要求せず、同じ可逆成分の合成を保持する。
使われ方：同じ Yoneda 恒等点・実 AsSmall 零単体から指定 G の元の射への回収。 -/
lemma rightFrameTerminalHomComparison_originalArrow {Y : C} (f : X ⟶ Y) :
    (c.triangle.toNatIso.app (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))).inv ≫
      (hoFunctor.map (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫
        c.equivalence.hom)).toFunctor.map
        (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) ≫
      (c.triangle.toNatIso.app (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))).hom =
      (hoFunctor.map G).toFunctor.map
        (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) :=
  modelRightFrameOriginalArrow_conjugation G X c.equivalence.hom c.triangle f

end SerrePositivity.EInfinity.FrameHom
