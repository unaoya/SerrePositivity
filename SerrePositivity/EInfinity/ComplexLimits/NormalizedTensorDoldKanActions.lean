module

public import SerrePositivity.EInfinity.ComplexLimits.DoldKanPinchedChainNaturality
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorHomBifunctor

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedTensorDoldKanIso_precomp {X X' : Complex A} (Y : Complex A) (f : X' ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((normalizedSimplexTensorFamily A).map f)).app Y ≫
      (normalizedSimplexTensorHomIso A X' Y).hom =
    (normalizedSimplexTensorHomIso A X Y).hom ≫
      doldKanHomSpaceChainMap (D := Complex A) (E := Complex A) (homPrecompose f Y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  exact normalizedSimplexTensorHomEquiv_precomp A Y f n.unop g

lemma normalizedTensorDoldKanIso_postcomp (X : Complex A) {Y Y' : Complex A} (f : Y ⟶ Y') :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).map f ≫
      (normalizedSimplexTensorHomIso A X Y').hom =
    (normalizedSimplexTensorHomIso A X Y).hom ≫
      doldKanHomSpaceChainMap (D := Complex A) (E := Complex A) (homPostcompose X f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  exact normalizedSimplexTensorHomEquiv_postcomp A X n.unop g f

end SerrePositivity.EInfinity.ComplexLimits
