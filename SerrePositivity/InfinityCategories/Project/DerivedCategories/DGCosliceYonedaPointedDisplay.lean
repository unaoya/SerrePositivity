module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPointedTransportRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTransportSquareFiberUniverse
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourcePointedFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
/-!
概要：元の実 coslice の Yoneda 指定点評価を、同じ全空間の実 pointed 表示で表す。
方針：始点固定 Tw の同じ比較を前合成し、同じ実 fiber 射の合成で全 fiber 同値を証明する。
規約：全単体族の実表示。使われ方：Hom 単位の表示との F1 分類比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
/-- 元の quasicategory の Yoneda 関手を指定始点で評価した、全空間値関手。 -/
def dgCosliceYonedaSpaceInfinity : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))
/-- 元の同じ coslice 全体からの、同じ Yoneda 評価の実 pointed 表示。 -/
def dgCosliceYonedaPointedDisplay :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourcePointedDisplay x
/-- 同じ実 pointed 表示の底は、元の同じ Yoneda 指定点評価。 -/
lemma dgCosliceYonedaPointedDisplay_projection :
    dgCosliceYonedaPointedDisplay X x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) ≫ dgCosliceYonedaSpaceInfinity X x := by
  rw [dgCosliceYonedaPointedDisplay, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourcePointedDisplay_projection,
    ← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection]
  rfl
/-- 元の同じ coslice の pointed 表示は、同じ全ての実 fiber 射で同値。 -/
lemma dgCosliceYonedaPointedDisplay_fiber_isQCatEquivalence (b : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)))
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (dgCosliceYonedaPointedDisplay X x)
      (dgCosliceYonedaSpaceInfinity X x) (dgCosliceYonedaPointedDisplay_projection X x)
      (ULift.up b)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection x
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource x
  have hf : f ≫ q = p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection x
  have h : f ≫ q = p ≫ 𝟙 X := hf.trans (Category.comp_id p).symm
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f (𝟙 X) h b) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q f hf
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isPrecompositionEquivalence x) b
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_ulift_isQCatEquivalence.{u, u + 1} p q f (𝟙 X) h b he
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourcePointedDisplayFiber_isQCatEquivalence x b
  let U := SSet.uliftFunctor.{u + 1, u}
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourcePointedDisplay x
  let G := dgCosliceYonedaSpaceInfinity X x
  have hU : U.map f ≫ U.map q = U.map p ≫ U.map (𝟙 X) := by
    rw [← Functor.map_comp, h, Functor.map_comp]
  have hW : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = U.map q ≫ G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourcePointedDisplay_projection x
  have hc : (U.map f ≫ W) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = U.map p ≫ (U.map (𝟙 X) ≫ G) := by
    rw [Category.assoc, hW, ← Category.assoc, hU, Category.assoc]
  have H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap (U.map p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f ≫ W) (U.map (𝟙 X) ≫ G) hc (ULift.up b)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_comp (U.map p) (U.map q) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f) (U.map (𝟙 X)) hU W G hW (ULift.up b)]
    exact hu.comp ht
  have hG : U.map (𝟙 X) ≫ G = dgCosliceYonedaSpaceInfinity X x := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_congr (U.map p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (U.map f ≫ W) (dgCosliceYonedaPointedDisplay X x)
    (U.map (𝟙 X) ≫ G) (dgCosliceYonedaSpaceInfinity X x) rfl hG hc
    (dgCosliceYonedaPointedDisplay_projection X x) (ULift.up b)).mp H
/-- 元の実 coslice を、同じ Yoneda 指定点評価で分類する実 transport 表現。 -/
def dgCosliceYonedaTransportRepresentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointedTransportRepresentation _ (dgCosliceYonedaSpaceInfinity X x)
    (dgCosliceYonedaPointedDisplay X x) (dgCosliceYonedaPointedDisplay_projection X x) (by
      rintro ⟨b⟩
      exact dgCosliceYonedaPointedDisplay_fiber_isQCatEquivalence X x b)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
