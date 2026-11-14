module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegValueComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.LargeTotalCoconeUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningOverMap

/-!
概要：有限検出の値射と標準余錐の元の脚を、同じ fiber 比較で照合する。
方針：元の余錐 fiber 写像の値比較と、全空間単位の保存済み同型を制限する。
規約：小さい fiber 同値の順方向は元の選択そのものを保持する。
使われ方：全空間の有限検出を native な脚へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 頂点の指定等式で移した全空間値写像も、同じ元の脚の作用と比較できる。 -/
def coconeFiberValueAt_leg_iso {B : SSet.{u + 1}} {F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (b : B _⦋0⦌) {z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (hz : c.vertex = z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberSource F b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt c z hz)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c b) ≫
            eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s)) hz))) := by
  cases hz
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt, eqToHom_refl, Category.id_comp,
    Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberMap, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberMap_valueIso c b

variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 小さい fiber の順方向を持ち上げると、構成元の二つの fiber 同型と値射を回収する。 -/
lemma smallFiberValue_hom_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberIso F b).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F (ULift.up b)).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence
            (F.app (Opposite.op ⦋0⦌) (ULift.up b))).hom := by
  change (SSet.uliftFunctor.{u + 1, u}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningLiftedFiberValueEquivalence F b).hom) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift]
  rfl

/-- 元の二つの fiber 同型に続く元の包含は、縮小した全空間の同じ包含。 -/
lemma smallFiberSource_factor :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberIso F b).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F (ULift.up b)).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberSource F (ULift.up b) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberSource]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberIso_hom_ι F b

/-- 標準余錐の実際の脚を、指定された全空間頂点の値で読む。 -/
def totalLegToVertexValue :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex F)).obj :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) (ULift.up b)) ≫
    eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s))
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex F))

/-- fiber の順方向で前合成した元の脚は、同じ fiber 包含と全空間単位に全比較される。 -/
def smallFiber_leg_unit_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b).hom ≫ totalLegToVertexValue F b))
      ((SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit F)) := by
  let P := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberIso F b).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F (ULift.up b)).hom
  have h₁ := (coconeFiberValueAt_leg_iso (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) (ULift.up b)
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex F)).precomp P
  have hs : P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegFiberSource F (ULift.up b) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).hom := smallFiberSource_factor F b
  have hv : P ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))).hom =
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b).hom :=
    (smallFiberValue_hom_lift F b).symm
  simp only [← Category.assoc] at h₁
  rw [hs, hv] at h₁
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalCoconeUnitIso F).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).hom)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalUnit, Category.assoc, Iso.hom_inv_id_assoc] at h₂
  simpa only [Functor.map_comp, totalLegToVertexValue, Category.assoc] using h₁.symm ≪≫ h₂

set_option maxHeartbeats 1000000 in
-- 頂点表示・縮小 fiber・ULift の型の同時展開が標準 heartbeat を超えるため。
/-- 同じ fiber 比較の全同型を元の小さい宇宙の Homotopy に戻す。 -/
def smallFiber_leg_unit_homotopy :
    Homotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b).hom ≫
      totalLegToVertexValue F b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.unliftSimplicialHomotopy (smallFiber_leg_unit_iso F b).simplicialHomotopy

/-- 元の標準余錐脚を、厳密な頂点表示の往復で全空間 Kan 模型へ移す。 -/
def totalLegToKan :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F :=
  totalLegToVertexValue F b ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object F)

/-- 同じ fiber 比較で前合成した脚は、元の置換単位による fiber 包含にホモトピック。 -/
def smallFiber_leg_toKan_homotopy :
    Homotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b).hom ≫ totalLegToKan F b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (smallFiber_leg_unit_homotopy F b)
    (eqToHom (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object F))
  simpa only [totalLegToKan, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit_factor] using H

/-- 有限検出で用いる元の値射は、同じ標準余錐の実際の脚とホモトピック。 -/
lemma totalLegToKan_homotopy_valueToTotal :
    Nonempty (Homotopy (totalLegToKan F b) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence F b
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp e.invHomIso.simplicialHomotopy (totalLegToKan F b)⟩
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (smallFiber_leg_toKan_homotopy F b) e.inv⟩
  simp only [Category.assoc, Category.id_comp] at h₀ h₁
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan, Category.assoc] using h₀.symm.trans h₁

/-- 全空間への有限射は、同じ標準余錐の元の一つの脚を経由してホモトピック。 -/
lemma finite_totalLeg_detection [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    {K : SSet.{u}} [K.Finite] (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) :
    ∃ b : B _⦋0⦌,
      ∃ g : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        Nonempty (Homotopy f (g ≫ totalLegToKan F b)) := by
  obtain ⟨b, g, H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredTotalKan_finite_value_detection F f
  obtain ⟨J⟩ := totalLegToKan_homotopy_valueToTotal F b
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr H
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp J g⟩
  exact ⟨b, g, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp (h₀.trans h₁.symm)⟩

/-- 標準余錐の頂点から読み戻した値と、元の全空間 Kan 模型の厳密な表示同型。 -/
def totalApexKanIso :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex).obj ≅ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F :=
  eqToIso (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s))
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone_vertex F)) ≪≫ eqToIso (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex_object F)

lemma totalLegToKan_eq_nativeLeg :
    totalLegToKan F b =
      @CategoryStruct.comp SSet.{u} _ _ _ _
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) (ULift.up b)))
        (totalApexKanIso F).hom := by
  simp only [totalLegToKan, totalLegToVertexValue, totalApexKanIso, Iso.trans_hom,
    eqToIso.hom, Category.assoc]

/-- 標準余錐の元の頂点値への有限射を、元の一つの脚で検出する。 -/
lemma finite_nativeTotalLeg_detection [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    {K : SSet.{u}} [K.Finite]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex).obj) :
    ∃ b : B _⦋0⦌,
      ∃ g : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        Nonempty (Homotopy f
          (g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) (ULift.up b)))) := by
  obtain ⟨b, g, ⟨H⟩⟩ := finite_totalLeg_detection F (f ≫ (totalApexKanIso F).hom)
  have J := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (totalApexKanIso F).inv
  rw [totalLegToKan_eq_nativeLeg] at J
  refine ⟨b, g, ⟨?_⟩⟩
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using J

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
