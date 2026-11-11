module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockComponent
public import SerrePositivity.EInfinity.FrameHom.LocalizationComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.RightFrameUnitFamily
public import SerrePositivity.EInfinity.FrameHom.SourceRoofUnitNormalization
public import SerrePositivity.EInfinity.SimplicialLocalization.HammockInvertsEdges

/-!
概要：同じ全圏 hammock の局所化普遍性を明示入力にした指定局所化の比較。
方針：元の六辺の全 coherent 比較と指定二胞体の端点輸送を合成する。
規約：この補助入口の普遍性入力は ModelRightFrameComparison の主入口で放電する。
使われ方：指定 K・二胞体を保つ主入口の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open SimplicialLocalization
open scoped Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (K : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K) G)

/-- 概要：全圏 hammock と指定局所化の比較は元の全二胞体を保持する。
方針：実局所化普遍性を明示した既存の一意性比較へ渡す。
規約：元の K と e を変更しない。使われ方：全族と端点輸送の同じ比較。 -/
def rightFrameSpecifiedLocalizationData :
    CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G :=
  localizationComparisonData _ G _ hH hG K e

/-- 概要：同じ指定局所化比較の二胞体は元の二胞体そのもの。
方針：束ねの定義を読む。
規約：厳密化しない。使われ方：Sp の全二胞体の合成。 -/
lemma rightFrameSpecifiedLocalizationData_triangle :
    (rightFrameSpecifiedLocalizationData G hG hH K e).triangle = e := rfl

/-- 概要：元の right Hom と指定局所化の pinched Hom の実 QCat 同値。
方針：同じ全 coherent 六辺の実成分と元の指定二胞体の端点共役を合成する。
規約：元の全圏の局所化像を保持し、hammock 普遍性は明示入力。
使われ方：その入力の供給後の条件の放電。 -/
def rightFrameSpecifiedPinchedEquivalence (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))
        (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))) :=
  (rightFrameHammockPinchedEquivalence q r cof Y).trans
    ((rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))

/-- 概要：同じ実比較は元の六辺の比較と同じ K の Hom 作用・指定成分の共役。
方針：合成同値の順射と元の端点輸送の定義を読む。
規約：元の指定二胞体の両端成分。使われ方：全族・零単体の同じ式の保持。 -/
lemma rightFrameSpecifiedPinchedEquivalence_hom (Y : C) :
    (rightFrameSpecifiedPinchedEquivalence q r cof G hG hH K e Y).hom =
      (rightFrameHammockPinchedEquivalence q r cof Y).hom ≫
        ((rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y))).hom :=
  rfl

end SerrePositivity.EInfinity.FrameHom
