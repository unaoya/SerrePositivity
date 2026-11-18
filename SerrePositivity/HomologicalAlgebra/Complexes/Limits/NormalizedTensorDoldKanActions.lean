module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanPinchedChainNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorHomBifunctor

/-!
# 元の正規化テンソル Hom と同じ実 Γ 前後作用の全単体整合

概要：元の複体射の前後作用は同じ Hom 鎖写像の実 Γ 像へ厳密に移る。
方針：既存の全次数の Hom 等式を単体写像の等式へ束ねる。
規約：元の normalizedSimplexTensorHomIso の射を使う。
使われ方：全複体 dg nerve の pinched Hom への前後作用の移送。
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

lemma normalizedTensorDoldKanIso_precomp {X X' : Complex A} (Y : Complex A) (f : X' ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamily A).map f)).app Y ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X' Y).hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X Y).hom ≫
      _root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap (D := Complex A) (E := Complex A) (homPrecompose f Y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv_precomp A Y f n.unop g

lemma normalizedTensorDoldKanIso_postcomp (X : Complex A) {Y Y' : Complex A} (f : Y ⟶ Y') :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).map f ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X Y').hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X Y).hom ≫
      _root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap (D := Complex A) (E := Complex A) (homPostcompose X f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv_postcomp A X n.unop g f

end SerrePositivity.ComplexLimits
