module
public import SerrePositivity.InfinityCategories.Derived.DGPointedTransportRepresentation
public import SerrePositivity.InfinityCategories.Derived.DGTransportSquareFiberUniverse
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourcePointedFiber
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
/-- 元の quasicategory の Yoneda 関手を指定始点で評価した、全空間値関手。 -/
def dgCosliceYonedaSpaceInfinity : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u} :=
  yonedaInfinityMap X ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))
/-- 元の同じ coslice 全体からの、同じ Yoneda 評価の実 pointed 表示。 -/
def dgCosliceYonedaPointedDisplay :
    (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder (SSet.yonedaEquiv.symm x)) ⟶
      PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (cosliceToTwistedArrowSource x) ≫
    twistedArrowSourcePointedDisplay x
/-- 同じ実 pointed 表示の底は、元の同じ Yoneda 指定点評価。 -/
lemma dgCosliceYonedaPointedDisplay_projection :
    dgCosliceYonedaPointedDisplay X x ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map
        (sliceUnderProjection (SSet.yonedaEquiv.symm x)) ≫ dgCosliceYonedaSpaceInfinity X x := by
  rw [dgCosliceYonedaPointedDisplay, Category.assoc, twistedArrowSourcePointedDisplay_projection,
    ← Category.assoc, ← Functor.map_comp, cosliceToTwistedArrowSource_projection]
  rfl
/-- 元の同じ coslice の pointed 表示は、同じ全ての実 fiber 射で同値。 -/
lemma dgCosliceYonedaPointedDisplay_fiber_isQCatEquivalence (b : X _⦋0⦌) :
    IsQCatEquivalence (transportSquareFiberMap
      ((SSet.uliftFunctor.{u + 1, u}).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
      pointedSpaceProjection (dgCosliceYonedaPointedDisplay X x)
      (dgCosliceYonedaSpaceInfinity X x) (dgCosliceYonedaPointedDisplay_projection X x)
      (ULift.up b)) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := twistedArrowSourceProjection x
  let f := cosliceToTwistedArrowSource x
  have hf : f ≫ q = p := cosliceToTwistedArrowSource_projection x
  have h : f ≫ q = p ≫ 𝟙 X := hf.trans (Category.comp_id p).symm
  have he : IsQCatEquivalence (transportSquareFiberMap p q f (𝟙 X) h b) := by
    exact vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q f hf
      (cosliceToTwistedArrowSource_isPrecompositionEquivalence x) b
  have hu := dgTransportSquareFiberMap_ulift_isQCatEquivalence.{u, u + 1} p q f (𝟙 X) h b he
  have ht := twistedArrowSourcePointedDisplayFiber_isQCatEquivalence x b
  let U := SSet.uliftFunctor.{u + 1, u}
  let W := twistedArrowSourcePointedDisplay x
  let G := dgCosliceYonedaSpaceInfinity X x
  have hU : U.map f ≫ U.map q = U.map p ≫ U.map (𝟙 X) := by
    rw [← Functor.map_comp, h, Functor.map_comp]
  have hW : W ≫ pointedSpaceProjection = U.map q ≫ G :=
    twistedArrowSourcePointedDisplay_projection x
  have hc : (U.map f ≫ W) ≫ pointedSpaceProjection = U.map p ≫ (U.map (𝟙 X) ≫ G) := by
    rw [Category.assoc, hW, ← Category.assoc, hU, Category.assoc]
  have H : IsQCatEquivalence (transportSquareFiberMap (U.map p) pointedSpaceProjection
      (U.map f ≫ W) (U.map (𝟙 X) ≫ G) hc (ULift.up b)) := by
    rw [dgTransportSquareFiberMap_comp (U.map p) (U.map q) pointedSpaceProjection
      (U.map f) (U.map (𝟙 X)) hU W G hW (ULift.up b)]
    exact hu.comp ht
  have hG : U.map (𝟙 X) ≫ G = dgCosliceYonedaSpaceInfinity X x := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (dgTransportSquareFiberMap_congr (U.map p) pointedSpaceProjection
    (U.map f ≫ W) (dgCosliceYonedaPointedDisplay X x)
    (U.map (𝟙 X) ≫ G) (dgCosliceYonedaSpaceInfinity X x) rfl hG hc
    (dgCosliceYonedaPointedDisplay_projection X x) (ULift.up b)).mp H
/-- 元の実 coslice を、同じ Yoneda 指定点評価で分類する実 transport 表現。 -/
def dgCosliceYonedaTransportRepresentation :
    LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))) :=
  dgPointedTransportRepresentation _ (dgCosliceYonedaSpaceInfinity X x)
    (dgCosliceYonedaPointedDisplay X x) (dgCosliceYonedaPointedDisplay_projection X x) (by
      rintro ⟨b⟩
      exact dgCosliceYonedaPointedDisplay_fiber_isQCatEquivalence X x b)
end SerrePositivity.InfinityCategories
