module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockLocalizedObjects
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonal
public import SerrePositivity.EInfinity.SimplicialLocalization.Hom
public import SerrePositivity.EInfinity.Hammock.FixedObjectLocalizationEvaluation

/-!
# 元の自由 hammock の対角から既存 DK Hom への右比較

概要：元の各自由次数の zigzag の局所化評価から DK 命題2.2の右射を構成する。
方針：全語の余極限からの自然な評価へ実際の自由対象の表示を代入し、対角を取る。
規約：既存 localizationHom の全作用素と同じ対象移送を使う。弱同値性は後続。
使われ方：元の hammock と既存 DK Hom の高次比較。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory

def freeHammockHomComparison (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockResolution C X Y ⟶ localizationHom C X Y ⋙ Functor.const SimplexCategoryᵒᵖ :=
  (freeHammockLocalizationObjects C).hammockEvaluation X Y

lemma freeHammockHomComparison_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n Y) w ≫
        (freeHammockHomComparison C X Y).app n =
          (freeHammockLocalizationObjects C).graphValue n w X Y :=
  (freeHammockLocalizationObjects C).colimitValue_fac n X Y w

def freeHammockDiagonalComparison (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonal C X Y ⟶ localizationHom C X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (freeHammockHomComparison C X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (localizationHom C X Y)).hom

lemma freeHammockDiagonalComparison_app (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (freeHammockDiagonalComparison C X Y).app n =
      ((freeHammockHomComparison C X Y).app n).app n := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
