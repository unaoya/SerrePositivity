module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoldKanActions

/-!
# 元の全複体の正規化 Hom と dg nerve の同じ pinched Hom の全作用

概要：実正規化 Hom と同じ全複体 dg nerve の pinched Hom を同定し、前後作用を保つ。
方針：元の実 DK 同型と任意 Hom 鎖写像への pinched 比較の自然性を合成する。
規約：cofibrancy や Small の入力なしに元の複体射を使う。
使われ方：自由単位と同じ全区間族の前合成の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def normalizedTensorPinchedIso (X Y : Complex A) :
    SSet.uliftFunctor.{u + 1, u}.obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y :=
  SSet.uliftFunctor.{u + 1, u}.mapIso (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X Y) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso X Y

lemma normalizedTensorPinchedIso_precomp {X X' : Complex A} (Y : Complex A) (f : X' ⟶ X) :
    SSet.uliftFunctor.{u + 1, u}.map
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamily A).map f)).app Y) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X' Y).hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPrecompose f Y) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoldKanIso_precomp,
    SSet.uliftFunctor.map_comp, Category.assoc, _root_.SerrePositivity.ComplexLimits.doldKanHomPinchedIso_chainMap]
  simp only [Category.assoc]

lemma normalizedTensorPinchedIso_postcomp (X : Complex A) {Y Y' : Complex A} (f : Y ⟶ Y') :
    SSet.uliftFunctor.{u + 1, u}.map
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).map f) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y').hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X f) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoldKanIso_postcomp,
    SSet.uliftFunctor.map_comp, Category.assoc, _root_.SerrePositivity.ComplexLimits.doldKanHomPinchedIso_chainMap]
  simp only [Category.assoc]

end SerrePositivity.ComplexLimits
