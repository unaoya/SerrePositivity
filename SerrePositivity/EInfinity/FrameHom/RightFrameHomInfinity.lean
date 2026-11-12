module

public import SerrePositivity.EInfinity.FrameHom.RightFrameTerminalHomReduction
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomInfinity

/-!
概要：right frame の終端から指定局所化の正本共変 Hom への全標的同型。
方針：同じ原本 Yoneda 全比較を代入し、同じ K・二胞体の全族輸送へ合成する。
規約：追加の Yoneda 存在入力も SSet のモデル構造も要求しない。
使われ方：Sp の β6 f4d の全標的自然性と任意図式への制限。
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

/-- 概要：同じ終端から指定 G の正本共変 Hom への全図式同型。
方針：条件付き補助入口の唯一の全比較入力を原本 Yoneda で放電する。
規約：同じ比較 K と指定二胞体を保持。
使われ方：全標的 Hom 図式の無条件の主入口。 -/
def rightFrameTerminalHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))) :=
  rightFrameTerminalHomIso_of_yonedaIso q r c
    (kanHammockHomInfinityIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))

/-- 概要：同じ全標的比較は任意の coherent 図式に沿う前合成でも保持される。
方針：同じ一つの全関手同型を前合成する。
規約：全高次自然性を保持。使われ方：Sp の固定した全添字図式への制限。 -/
def rightFrameTerminalHomIso_precomp {J : SSet.{max u v + 1}}
    (f : J ⟶ SSet.uliftFunctor.{max u v + 1, max u v}.obj
      (nerve (AsSmall.{max u v} C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ rightFrameHammockCoherentDiagram q r 6)
      (f ≫ SSet.uliftFunctor.{max u v + 1, max u v}.map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))) :=
  (rightFrameTerminalHomIso q r c).precomp f

end SerrePositivity.EInfinity.FrameHom
