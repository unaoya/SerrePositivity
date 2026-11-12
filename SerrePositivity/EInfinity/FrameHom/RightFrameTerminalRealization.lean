module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockCoherent
public import SerrePositivity.EInfinity.FrameHom.AsSmallHammockHomFamily
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomCoherent
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelRelative

/-!
概要：元の right frame 全比較の終端を同じ hammock 豊穣 Hom の実現へ同定する。
方針：元の AsSmall 全自然同型と元の源関手での全図式等式を合成する。
規約：終端の元の七段階図式を変更せず、点ごとの弱同値を使用しない。
使われ方：原本の Yoneda 全比較と指定局所化の全二胞体の代入。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SerrePositivity.EInfinity.SimplicialLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ終端図式と同じ hammock Hom の coherent 実現の源制限の全自然同型。
方針：同じ実 AsSmall 自然変換と全次数の源等式を使う。
規約：全標的を保持、未証明の Yoneda 比較は追加入力にしない。
使われ方：正本の共変 Hom と比較する前の同じ終端の回収。 -/
def rightFrameHammockTerminalRealizationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) ≫
          kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) := by
  rw [kanHammockHomCoherent_source]
  exact asSmallHammockHomCoherentIso (weakEquivalences C) X

/-- 概要：同じ終端の比較は任意の全標的図式への制限を保持する。
方針：構成済みの一つの全自然同型を前合成する。
規約：任意の単体集合のパラメータ。使われ方：Sp の全図式の自然性。 -/
def rightFrameHammockTerminalRealizationIso_precomp {J : SSet.{max u v + 1}}
    (f : J ⟶ SSet.uliftFunctor.{max u v + 1, max u v}.obj
      (nerve (AsSmall.{max u v} C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ rightFrameHammockCoherentDiagram q r 6)
      (f ≫ SSet.uliftFunctor.{max u v + 1, max u v}.map
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) ≫
          kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) :=
  (rightFrameHammockTerminalRealizationIso q r).precomp f

end SerrePositivity.EInfinity.FrameHom
