module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransport

/-!
概要：元の cocartesian 相対 Hom の全作用を strict transport 間の変換空間へ束ねる。
方針：各 undercategory の section への後合成を、同じ前合成の自然性で結ぶ。
規約：元の単位・合成と全高次パラメーターを保つ。比較の同値性は別途証明する。
使われ方：Cat∞ 値分類の写像空間比較と、その scaffold による回収。

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

/-- 全 cocartesian 相対 Hom を、同じ strict transport 図式間の変換空間へ写す。 -/
def cocartesianStrictTransportMappingSpaceMap {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q) where
  app n := ↾fun x ↦ ⟨fun c ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom
    (Over.mk (nerveMap (Under.forget c))) (Over.mk p) (Over.mk q)).app n x, by
      intro c d f k α y
      apply Subtype.ext
      apply Subtype.ext
      rfl⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro d β
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- 同じ比較射の各成分は、元の cocartesian section への全後合成そのもの。 -/
lemma cocartesianStrictTransportMappingSpaceMap_component
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) (c : C) :
    cocartesianStrictTransportMappingSpaceMap p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q) c =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget c)))
          (Over.mk p) (Over.mk q) := rfl

/-- 全相対 Hom から図式間の変換空間への同じ比較は豊穣単位を保つ。 -/
lemma cocartesianStrictTransportMappingSpaceMap_identity
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorIdentity (Over.mk p) ≫
      cocartesianStrictTransportMappingSpaceMap p p =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
  intro c
  rw [Category.assoc, cocartesianStrictTransportMappingSpaceMap_component,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component]
  rfl

/-- 全相対 Hom から図式間の変換空間への同じ比較は豊穣合成を保つ。 -/
lemma cocartesianStrictTransportMappingSpaceMap_composition
    {C : Type u} [Category.{u} C] {E D T : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) (r : T ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r) ≫
      cocartesianStrictTransportMappingSpaceMap p r =
      (cocartesianStrictTransportMappingSpaceMap p q ⊗ₘ
        cocartesianStrictTransportMappingSpaceMap q r) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram r) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
  intro c
  rw [Category.assoc, cocartesianStrictTransportMappingSpaceMap_component,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_component, ← Category.assoc,
    tensorHom_comp_tensorHom, cocartesianStrictTransportMappingSpaceMap_component,
    cocartesianStrictTransportMappingSpaceMap_component]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPostHom_comp (Over.mk (nerveMap (Under.forget c)))
    (Over.mk p) (Over.mk q) (Over.mk r)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
