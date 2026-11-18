module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameSpecifiedLocalization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockUnitComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallArrow
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockArrowNormalization

/-!
概要：指定局所化への実 frame 比較は元の局所化射の同じ零単体を保持する。
方針：同じ六辺の単位公式を元の AsSmall 射へ回収し、指定二胞体の比較を後合成する。
規約：指定 K と二胞体を保持し、生の辺の厳密化を要求しない。
使われ方：Sp の元の射・端点成分による共役の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (f : X ⟶ Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex

/-- 概要：実 frame 比較の元の単位点は元の持ち上げた通常射の coherent Hom 点と一致する。
方針：同じ六辺の単位公式と Ex∞ 単位の自然性・元の宇宙比較を合成する。
規約：anodyne 反転後の同じ零単体。
使われ方：元の hammock 源関手の射の回収。
-/
lemma rightFrameHammockPinchedEquivalence_unit_arrow_Q :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 0 ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence q r cof Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)) := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom)
  simp only [Functor.id_map] at h
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (weakEquivalences C) X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak (weakEquivalences C)) (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak (weakEquivalences C))
          (AsSmall.up.obj X) (AsSmall.up.obj Y))
    exact h.symm.trans (by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak (weakEquivalences C))
            (AsSmall.up.obj X) (AsSmall.up.obj Y)))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.arrowMap_colimitIso (weakEquivalences C) f))
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence_unit_Q q r f cof).trans
    (congrArg AnodyneHomotopy.anodyneQ.map
      (by simpa only [Category.assoc] using congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)) ha))

variable {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (K : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K) G)

/-- 概要：指定局所化への同じ実比較は元の射を同じ指定二胞体で共役した点へ送る。
方針：元の局所化辺の零単体公式へ同じ K と両端成分の作用を後合成する。
規約：指定 K・二胞体 e を保持し、選択した逆を変更しない。
使われ方：全 coherent 比較の零単体と元の G の射の整合。
-/
lemma rightFrameSpecifiedPinchedEquivalence_unit_Q :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 0 ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedPinchedEquivalence q r cof G hG hH K e Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y) ≫
            ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y))).hom) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedPinchedEquivalence_hom]
  have h := congrArg (fun t => t ≫ AnodyneHomotopy.anodyneQ.map
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameSpecifiedLocalizationData G hG hH K e).pinchedEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y))).hom)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockPinchedEquivalence_unit_arrow_Q q r f cof)
  simpa only [Functor.map_comp, Category.assoc] using h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
