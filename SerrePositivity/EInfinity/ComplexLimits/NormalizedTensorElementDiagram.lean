module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Opposite
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev normalizedTensorElementIndex :=
  ULiftHom.{u} (ULift.{u + 1}
    ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ))

instance normalizedTensorElementIndexCategory :
    Category.{u} (normalizedTensorElementIndex A X Y) := inferInstance

def normalizedTensorElementDegree : normalizedTensorElementIndex A X Y ⥤ SimplexCategory :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙
    (Functor.Elements.π ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y)).leftOp

def normalizedTensorElementDiagram : normalizedTensorElementIndex A X Y ⥤ Complex A :=
  normalizedTensorElementDegree A X Y ⋙ normalizedSimplexTensor A X

def normalizedTensorElementAugmentation : normalizedTensorElementDiagram A X Y ⟶
    (Functor.const (normalizedTensorElementIndex A X Y)).obj X :=
  Functor.whiskerLeft (normalizedTensorElementDegree A X Y)
    (normalizedSimplexTensorAugmentation A X)

def normalizedTensorElementEvaluation : normalizedTensorElementDiagram A X Y ⟶
    (Functor.const (normalizedTensorElementIndex A X Y)).obj Y where
  app s := (ULiftHom.objDown s).down.unop.val
  naturality {s t} f := by
    change (normalizedSimplexTensor A X).map
      (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop ≫
        (ULiftHom.objDown t).down.unop.val =
        (ULiftHom.objDown s).down.unop.val ≫ 𝟙 Y
    exact (ULift.downFunctor.map (ULiftHom.down.map f)).unop.map_val.trans
      (Category.comp_id _).symm

lemma normalizedTensorElementAugmentation_quasiIso (s : normalizedTensorElementIndex A X Y) :
    QuasiIso ((normalizedTensorElementAugmentation A X Y).app s) :=
  normalizedSimplexTensorAugmentation_quasiIso A X (ULiftHom.objDown s).down.unop.obj.unop

lemma normalizedTensorElementDiagram_map_quasiIso
    {s t : normalizedTensorElementIndex A X Y} (f : s ⟶ t) :
    QuasiIso ((normalizedTensorElementDiagram A X Y).map f) :=
  normalizedSimplexTensor_map_quasiIso A X
    (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop

end SerrePositivity.EInfinity.ComplexLimits
