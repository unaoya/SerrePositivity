module

public import SerrePositivity.KST.Spectra.D3CommonStageLoop
public import SerrePositivity.KST.Spectra.PointedIhomActionNaturality
public import SerrePositivity.KST.Spectra.EndpointCircle
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom

/-!
概要：点つき Kan 複体上で、元の Hom パラメータと制限射の全自然性を保持する。
方針：既存の内部 Hom の豊穣作用を Kan 全部分圏へ制限し、源制限の厳密自然性を使う。
規約：円交換因子を比較しない。通常円と端点円の表示同型のみを全 Hom で移す。
使われ方：d3b② の実段 loop 図式と通常の点つき loop ∞ 作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3KanIhomPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 任意の元の点つきパラメータからの内部 Hom の、同じ Kan 豊穣作用。 -/
def d3PointedKanIhom (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} PointedKanObject.{u} PointedKanObject.{u} where
  obj X := ⟨PointedObject.basedHom A X.obj, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A X.obj⟩
  map X Y := (PointedMapping.ihomSimplicialFunctor A).map X.obj Y.obj
  map_id X := (PointedMapping.ihomSimplicialFunctor A).map_id X.obj
  map_comp X Y Z := (PointedMapping.ihomSimplicialFunctor A).map_comp X.obj Y.obj Z.obj

/-- 元の制限射は、同じ入力 Hom の全単体で自然。 -/
lemma d3PointedKanPre_whiskered {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X Y : PointedKanObject.{u}) :
    (d3PointedKanIhom B).map X Y ≫ eHomWhiskerLeft SSet
        ((d3PointedKanIhom B).obj X)
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj) :
          (d3PointedKanIhom B).obj Y ⟶ (d3PointedKanIhom A).obj Y) =
      (d3PointedKanIhom A).map X Y ≫ eHomWhiskerRight SSet
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) :
          (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom A).obj X)
        ((d3PointedKanIhom A).obj Y) := by
  have h := congrArg Under.Hom.right (PointedMapping.ihomAction_restrict i X.obj Y.obj)
  simp only [Under.comp_right] at h
  change (PointedMapping.ihomAction B X.obj Y.obj).right ≫
      eHomWhiskerLeft SSet (PointedObject.basedHom B X.obj)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj) =
    (PointedMapping.ihomAction A X.obj Y.obj).right ≫
      eHomWhiskerRight SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj)
        (PointedObject.basedHom A Y.obj)
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq]
  exact h

/-- 同じパラメータ制限を成分とする実豊穣自然変換。 -/
def d3PointedKanPre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (d3PointedKanIhom B) (d3PointedKanIhom A) where
  app X := eHomEquiv SSet (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj))
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj)
    ((d3PointedKanIhom A).map X Y) ((d3PointedKanIhom B).map X Y)).mp
      (d3PointedKanPre_whiskered i X Y).symm).symm

/-- coherent な変換でも、成分は同じ元のパラメータ制限射。 -/
lemma d3PointedKanPre_component {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X : PointedKanObject.{u}) :
    StrictEnrichedTransformation.componentHom (d3PointedKanIhom B) (d3PointedKanIhom A)
      (d3PointedKanPre i) X = ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) :
        (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom A).obj X))) = _
  exact Equiv.symm_apply_apply _ _

/-- パラメータ表示同型の同じ制限射は、元の Kan Hom 上で全基点 π 同型。 -/
lemma d3PointedKanPre_piIsomorphism {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) [IsIso i]
    (X : PointedKanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj).right := by
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    change IsIso ((internalHom.flip.obj X.obj).map i.op)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
    ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso _)

/-- 同じパラメータ表示同型を制限する全関手同型。 -/
def d3PointedKanPreFunctorIso {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) [IsIso i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom A)) :=
  StrictEnrichedTransformation.functorIso _ _ (d3PointedKanPre i) (fun X ↦ by
    rw [d3PointedKanPre_component]
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _ (d3PointedKanPre_piIsomorphism i X))

/-- 通常円の同じ全 Hom 作用は、既存の点つき Kan loop 作用そのもの。 -/
lemma d3PointedKanIhom_circle :
    d3PointedKanIhom PointedSimplicialSet.circle.{u} = pointedKanLoopEnrichedFunctor := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro X; rfl
  case h_map =>
    intro X Y
    simp only [eqToHom_refl, Category.comp_id]
    exact d3Stage_loop_action X Y

/-- 通常の点つき loop ∞ 作用と端点円模型を、同じ表示同型から全関手比較する。 -/
def d3PointedKanEndpointLoopIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso pointedKanLoopInfinity.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle)) := by
  have e := d3PointedKanPreFunctorIso endpointCircleIso.{u}.hom
  rw [d3PointedKanIhom_circle] at e
  exact e

/-- 同じパラメータ制限が全入力 Hom に誘導する実際の混合 Hom 作用。 -/
def d3PointedKanMixed {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X Y : PointedKanObject.{u}) :
    SimplicialCategory.sHom X Y ⟶
      SimplicialCategory.sHom ((d3PointedKanIhom B).obj X) ((d3PointedKanIhom A).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom (d3PointedKanPre i) X Y

/-- 恒等パラメータの混合 Hom は、元の内部 Hom の作用そのもの。 -/
lemma d3PointedKanMixed_id (A : PointedSimplicialSet.{u}) (X Y : PointedKanObject.{u}) :
    d3PointedKanMixed (𝟙 A) X Y = (d3PointedKanIhom A).map X Y := by
  have hi : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 A) X.obj = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact (internalHom.flip.obj X.obj).map_id (Opposite.op A)
  dsimp only [d3PointedKanMixed, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom, d3PointedKanPre]
  rw [hi]
  change (λ_ _).inv ≫ (eId SSet _ ⊗ₘ (d3PointedKanIhom A).map X Y) ≫ eComp SSet _ _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_id_comp, Iso.inv_hom_id_assoc]

/-- 元の二制限の因子分解は、同じ graded 成分の厳密合成。 -/
lemma d3PointedKanPre_factorization {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : C ⟶ A) (X : PointedKanObject.{u}) :
    (d3PointedKanPre (j ≫ i)).app X = (λ_ (𝟙_ SSet.{u})).inv ≫
      ((d3PointedKanPre i).app X ⊗ₘ (d3PointedKanPre j).app X) ≫
        eComp SSet ((d3PointedKanIhom B).obj X) ((d3PointedKanIhom A).obj X)
          ((d3PointedKanIhom C).obj X) := by
  change eHomEquiv SSet (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ i) X.obj) :
    (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom C).obj X) = _
  let f : (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom A).obj X :=
    ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj)
  let g : (d3PointedKanIhom A).obj X ⟶ (d3PointedKanIhom C).obj X :=
    ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j X.obj)
  have hfg : (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ i) X.obj) :
      (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom C).obj X) = f ≫ g := by
    apply ObjectProperty.hom_ext
    exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp j i X.obj).symm
  exact (congrArg (eHomEquiv SSet) hfg).trans (eHomEquiv_comp SSet f g)

/-- 二つの実混合 Hom の合成は、元のパラメータ合成と全 Hom 合成を同時に保持。 -/
lemma d3PointedKanMixed_comp {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : C ⟶ A) (X Y Z : PointedKanObject.{u}) :
    eComp SSet X Y Z ≫ d3PointedKanMixed (j ≫ i) X Z =
      (d3PointedKanMixed i X Y ⊗ₘ d3PointedKanMixed j Y Z) ≫
        eComp SSet ((d3PointedKanIhom B).obj X) ((d3PointedKanIhom A).obj Y)
          ((d3PointedKanIhom C).obj Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_factorization (d3PointedKanPre i) (d3PointedKanPre j)
    (d3PointedKanPre (j ≫ i)) (d3PointedKanPre_factorization i j) X Y Z

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
