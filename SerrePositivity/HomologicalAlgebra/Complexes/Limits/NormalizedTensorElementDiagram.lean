module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：元の正規化 Hom の全単体と全作用素を、同じ実屋根の図式へ束ねる。
方針：反対要素圏の次数射影を元の frame に代入し、同じ augmentation と評価を使う。
規約：全単体と元の二本の射を保つ。
使われ方：局所単体ごとの評価を大域的な全自然変換と照合するための実図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.Opposite
attribute [local instance] uliftCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev normalizedTensorElementIndex :=
  ULiftHom.{u} (ULift.{u + 1}
    ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ))

instance normalizedTensorElementIndexCategory :
    Category.{u} (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) := inferInstance

def normalizedTensorElementDegree : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y ⥤ SimplexCategory :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙
    (Functor.Elements.π ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y)).leftOp

def normalizedTensorElementDiagram : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y ⥤ Complex A :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y ⋙ _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X

def normalizedTensorElementAugmentation : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⟶
    (Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj X :=
  Functor.whiskerLeft (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X)

def normalizedTensorElementEvaluation : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⟶
    (Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj Y where
  app s := (ULiftHom.objDown s).down.unop.val
  naturality {s t} f := by
    change (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map
      (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop ≫
        (ULiftHom.objDown t).down.unop.val =
        (ULiftHom.objDown s).down.unop.val ≫ 𝟙 Y
    exact (ULift.downFunctor.map (ULiftHom.down.map f)).unop.map_val.trans
      (Category.comp_id _).symm

lemma normalizedTensorElementAugmentation_quasiIso (s : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app s) :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation_quasiIso A X (ULiftHom.objDown s).down.unop.obj.unop

lemma normalizedTensorElementDiagram_map_quasiIso
    {s t : _root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y} (f : s ⟶ t) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map f) :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_map_quasiIso A X
    (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop

end SerrePositivity.ComplexLimits
