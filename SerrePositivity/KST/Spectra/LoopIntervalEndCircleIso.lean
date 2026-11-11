module

public import SerrePositivity.KST.Spectra.IntervalEndpointFamilies
public import SerrePositivity.KST.Spectra.CofiberMappingFamilies
public import SerrePositivity.KST.Spectra.LoopPathFiber

/-!
概要：区間重みの end と基点付き円からの写像空間を厳密に同定する。
方針：両端の定数性で商へ降下し、逆向きは商写像に沿った評価族を end へ持ち上げる。
規約：Kan 性は不要で、元の区間上の評価を保持する。使われ方：円評価の BF 比較の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

/-- 区間の end の普遍族を、両端を潰した円からの基点付き写像空間へ降ろす。 -/
def loopIntervalEndToCircleMapping (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) ⟶
      (PointedObject.basedHom endpointCircle Y).right :=
  cofiberFamilyDesc _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right Y (loopIntervalEndFamily Y) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]
    exact (intervalFamily_boundary_iff _ _).mpr
      ⟨loopIntervalEndFamily_left Y, loopIntervalEndFamily_right Y⟩)

/-- 円からの写像空間の、元の区間上の評価族。 -/
def endpointCircleMappingFamily (Y : PointedSimplicialSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (PointedObject.basedHom endpointCircle Y).right ⟶ Y.right :=
  uncurry (PointedObject.basedHomι endpointCircle Y ≫
    (pre (PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right)).app Y.right)

/-- 元の区間上の評価族は、境界全体を標的の基点へ送る。 -/
lemma endpointCircleMappingFamily_boundary (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ▷ _) ≫ endpointCircleMappingFamily Y =
      SSet.const Y.basepoint := by
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const, endpointCircleMappingFamily] using
    cofiberFamily_restriction_boundary _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right Y
      (𝟙 (PointedObject.basedHom endpointCircle Y).right)

/-- 商の評価族を、元の区間 end へ持ち上げる。 -/
def circleMappingToLoopIntervalEnd (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom endpointCircle Y).right ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) :=
  loopIntervalEndLift Y (endpointCircleMappingFamily Y)
    ((intervalFamily_boundary_iff _ _).mp (endpointCircleMappingFamily_boundary Y)).1
    ((intervalFamily_boundary_iff _ _).mp (endpointCircleMappingFamily_boundary Y)).2

/-- 円の評価族を持ち上げた end の中央射影は、元の区間への制限そのもの。 -/
@[reassoc]
lemma circleMappingToLoopIntervalEnd_central (Y : PointedSimplicialSet.{u}) :
    circleMappingToLoopIntervalEnd Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one) =
      PointedObject.basedHomι endpointCircle Y ≫
        (pre (PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right)).app Y.right := by
  rw [circleMappingToLoopIntervalEnd, loopIntervalEndLift_central]
  exact curry_uncurry _

/-- 円への降下を区間に制限すると、元の end の中央射影になる。 -/
@[reassoc]
lemma loopIntervalEndToCircleMapping_restriction (Y : PointedSimplicialSet.{u}) :
    loopIntervalEndToCircleMapping Y ≫ PointedObject.basedHomι endpointCircle Y ≫
        (pre (PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right)).app Y.right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one) := by
  rw [loopIntervalEndToCircleMapping, cofiberFamilyDesc_restriction]
  change curry (uncurry (𝟙 _ ≫ _)) = _
  rw [Category.id_comp, curry_uncurry]

/-- 区間 end と、二端点を潰した円からの基点付き写像空間の厳密な同型。 -/
def loopIntervalEndEndpointCircleIso (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) ≅
      (PointedObject.basedHom endpointCircle Y).right where
  hom := loopIntervalEndToCircleMapping Y
  inv := circleMappingToLoopIntervalEnd Y
  hom_inv_id := by
    apply loopIntervalEnd_hom_ext
    rw [Category.id_comp, Category.assoc]
    change loopIntervalEndToCircleMapping Y ≫ (loopIntervalEndLift Y _ _ _) ≫ _ = _
    rw [loopIntervalEndLift_central, ← curry_natural_left]
    dsimp only [endpointCircleMappingFamily]
    rw [← uncurry_natural_left, curry_uncurry]
    exact loopIntervalEndToCircleMapping_restriction Y
  inv_hom_id := by
    apply cofiberFamily_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right Y
    rw [Category.id_comp, Category.assoc, loopIntervalEndToCircleMapping_restriction]
    change loopIntervalEndLift Y _ _ _ ≫ _ = _
    rw [loopIntervalEndLift_central]
    exact curry_uncurry _

/-- 区間 end は、標準の基点付き円からの写像空間と厳密に同型。 -/
def loopIntervalEndCircleIso (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) ≅ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right :=
  loopIntervalEndEndpointCircleIso Y ≪≫
    (PointedSimplicialSet.forget.mapIso (loopToEndpointHomIso Y)).symm

/-- 同型の逆を中央へ射影すると、標準の円への商写像に沿う元の制限になる。 -/
@[reassoc]
lemma loopIntervalEndCircleIso_inv_central (Y : PointedSimplicialSet.{u}) :
    (loopIntervalEndCircleIso Y).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one) =
      PointedObject.basedHomι PointedSimplicialSet.circle Y ≫
        (pre (PointedObject.cofiberQuotient (boundary.{u} 1).ι)).app Y.right := by
  change (loopToEndpointHomIso Y).hom.right ≫ circleMappingToLoopIntervalEnd Y ≫ _ = _
  rw [circleMappingToLoopIntervalEnd_central, ← Category.assoc]
  have hp : (loopToEndpointHomIso Y).hom.right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre endpointCircleIso.{u}.hom Y := by
    change ((MonoidalClosed.pre endpointCircleIso.{u}.hom).app Y).right = _
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    rfl
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  have hq : PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ≫
      endpointCircleIso.{u}.hom.right = PointedObject.cofiberQuotient (boundary.{u} 1).ι :=
    PointedObject.cofiberQuotient_desc _ _ _ _
  rw [hq]

end SerrePositivity.KST.Spectra
