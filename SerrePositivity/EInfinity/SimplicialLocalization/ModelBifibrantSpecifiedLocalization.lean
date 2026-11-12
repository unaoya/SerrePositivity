module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantLocalization
public import SerrePositivity.EInfinity.FrameHom.LocalizationComparison

/-!
概要：一般モデルの bifibrant hammock を指定された同じ弱同値の ∞ 局所化へ送る。
方針：実 right Kan 判定で得た普遍性を既存の局所化比較へ代入する。
規約：指定比較関手と指定二胞体を保持し、厳密な等式へ置き換えない。
使われ方：全 frame 比較の指定 pinched Hom への輸送と dg 代数への特殊化。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
  (K : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ K) G)

/-- 概要：実 bifibrant hammock と指定局所化の全比較を同じ二胞体で束ねる。
方針：余終性条件を放電済みの実局所化普遍性を既存の一意性へ渡す。
規約：比較関手 K と二胞体 e を変更しない。
使われ方：全 Hom 族と局所化像の零単体の比較。 -/
def modelBifibrantSpecifiedLocalizationComparison :
    FrameHom.CoherentLocalizationComparison
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G :=
  FrameHom.localizationComparisonData _ G _ (modelBifibrantHammock_isLocalization r) hG K e

/-- 概要：公開比較の全二胞体は元の指定二胞体そのもの。
方針：同じ束ねの定義を読む。
規約：定義上の等式。使われ方：Sp の coherent な二胞体の合成。 -/
lemma modelBifibrantSpecifiedLocalizationComparison_triangle :
    (modelBifibrantSpecifiedLocalizationComparison r G hG K e).triangle = e := rfl

/-- 概要：同じ指定二胞体を保持した実 pinched Hom の QCat 同値。
方針：同じ全比較 K の Hom 作用と両端の指定成分の共役を使う。
規約：元の局所化像の頂点を保持。使われ方：実 frame 比較の指定局所化への輸送。 -/
def modelBifibrantSpecifiedPinchedEquivalence (X Y : BifibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex X) (modelBifibrantHammockVertex Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X)))
        (G.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)))) :=
  (modelBifibrantSpecifiedLocalizationComparison r G hG K e).pinchedEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))

end SerrePositivity.EInfinity.SimplicialLocalization
