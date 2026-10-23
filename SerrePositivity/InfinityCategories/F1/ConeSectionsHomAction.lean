module

public import SerrePositivity.InfinityCategories.F1.CoherentSectionsConeMapEquivalence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.F1.TransportPrismLiftEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaceModelEquivalence

/-!
概要：元の全切断写像への後合成と全右 Hom の輸送を、全試験空間で同値にする。
方針：指定頂点の等式を消去し、元の射の同値性を内部 Hom へ移す。
規約：元の右 Hom・選択済み輸送族・全切断写像を使う。
使われ方：native な全 Hom 比較の同値性を結論するための合成側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
local instance {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)

/-- 元の頂点を等式で表示しても全切断写像の同値性は変わらない。 -/
lemma coneSectionsMapAt_isQCatEquivalence_iff {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌)
    (hv : c.vertex = z) :
    IsQCatEquivalence (coneSectionsMapAt c z hv) ↔ IsQCatEquivalence (coneSectionsMap c) := by
  cases hv
  rfl

/-- 元の全右 Hom の標準区間比較に沿う、選択済みの普遍輸送の作用は同値。 -/
lemma pointedRightHomTransport_isQCatEquivalence (x y : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (F2.pointedIntervalTransport (pinchedHomToIntervalMappingSpace x y)).map := by
  let a := pinchedHomToIntervalMappingSpace x y
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  apply pointedTransportFamily_map_isQCatEquivalence (𝟙 _)
    (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
    (intervalMappingUncurry a) (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)
  rw [hc]
  exact pinchedHomToIntervalMappingSpace_isQCatEquivalence x y

/-- 同じ錐の頂点の元の fiber から全切断への標準写像は同値。 -/
lemma coherentSectionsConeMap_isQCatEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (coneSectionsMap (coherentDiagramSectionsCone F)) :=
  (coneSectionsMapAt_isQCatEquivalence_iff _ _ (coherentDiagramSectionsCone_vertex F)).mp
    (coherentSectionsConeMapAt_isQCatEquivalence F)

/-- 元の全右 Hom の輸送と、同じ錐の全切断写像による後合成。 -/
def coneSectionsHomAction {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :=
  (F2.pointedIntervalTransport (pinchedHomToIntervalMappingSpace z c.vertex)).map ≫
    (ihom (vertexFiber pointedSpaceProjection z)).map (coneSectionsMap c)

/-- 全切断の実現錐の同じ Hom 作用は、任意の試験空間について同値。 -/
lemma coherentSectionsConeHomAction_isQCatEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (coneSectionsHomAction (coherentDiagramSectionsCone F) z) := by
  have : KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
    HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)
  exact (pointedRightHomTransport_isQCatEquivalence z _).comp
    ((coherentSectionsConeMap_isQCatEquivalence F).postcompose _)

end SerrePositivity.InfinityCategories
