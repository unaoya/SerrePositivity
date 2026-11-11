module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportMapping
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramPostcomposition

/-!
概要：cocartesian strict transport を元の全 section の strict transport に含める。
方針：全部分複体の包含の自然性を通常の図式へ束ね、全変換空間へ後合成する。
規約：包含は各次数で単射。図式の充填性は要求しない。
使われ方：cocartesian scaffold の逆比較を元の scaffold の往復の等式へ戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- cocartesian section の包含は strict transport の図式全体で自然。 -/
def cocartesianStrictTransportInclusion {C : Type u} [Category.{u} C]
    {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q where
  app c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι q (nerveMap (Under.forget c))
  naturality c d f := by
    let i : Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)) :=
      Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_ι q i

/-- 包含を strict な変換空間で後合成すると、同じ成分の内部 Hom の包含となる。 -/
lemma strictDiagramMappingPost_cocartesianInclusion_component
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {D : SSet.{u}}
    (q : D ⟶ nerve C) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (cocartesianStrictTransportInclusion q) F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q) c ≫
        (ihom (F.obj c)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι q (nerveMap (Under.forget c))) := rfl

/-- cocartesian section の包含による strict な変換空間の射は単射。 -/
instance strictDiagramMappingPost_cocartesianInclusion_mono
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {D : SSet.{u}}
    (q : D ⟶ nerve C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (cocartesianStrictTransportInclusion q) F) where
  right_cancellation := by
    intro Z f g h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
    intro c
    apply (cancel_mono
      ((ihom (F.obj c)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι q (nerveMap (Under.forget c))))).1
    have hc := congrArg (fun H => H ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) c) h
    simpa only [Category.assoc,
      strictDiagramMappingPost_cocartesianInclusion_component] using hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
