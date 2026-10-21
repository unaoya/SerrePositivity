module
public import SerrePositivity.InfinityCategories.Derived.DGTransportSquareFiberUniverse
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetCosliceFiberEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1.TwistedArrowSourceInitial
/-!
概要：同じ Hom 単位から作る実 pointed 表示は、全ての実 fiber で同値。
方針：元の実 coslice 比較を持ち上げ、同じ Tw 比較と pointed 比較の全 fiber 同値を合成する。
規約：各点で同値を選ぶのではなく、同じ全単体表示の実 fiber 射を証明する。
使われ方：F1 Hom 関手族との全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
open DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x : C)
/-- 同じ実 Hom 単位による持ち上げた pointed 表示の全ての実 fiber 射は全空間同値。 -/
lemma dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence (b : (dgNerve R C) _⦋0⦌) :
    IsQCatEquivalence (transportSquareFiberMap
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x))))
      pointedSpaceProjection (dgHomTargetCoslicePointedDisplay R C x)
      (dgHomTargetUnderlyingSpaceInfinity R C x)
      (dgHomTargetCoslicePointedDisplay_projection R C x) (ULift.up b)) := by
  let p := sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x))
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R C))
  let r := twistedArrowSourceProjection (dgHomModuleUnitVertex R C)
  let f := dgHomTargetCosliceComparison R C x
  let g := dgNerve.map (dgHomTargetModuleLift R C x)
  let f2 := cosliceToTwistedArrowSource (dgHomModuleUnitVertex R C)
  have hf : f ≫ q = p ≫ g := dgHomTargetCosliceComparison_projection R C x
  have hf2 : f2 ≫ r = q := cosliceToTwistedArrowSource_projection _
  have hf2' : f2 ≫ r = q ≫ 𝟙 _ := hf2.trans (Category.comp_id q).symm
  have hT (a : (dgHomModuleNerve R C) _⦋0⦌) :
      IsQCatEquivalence (transportSquareFiberMap q r f2 (𝟙 _) hf2' a) := by
    exact vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence q r f2 hf2
      (cosliceToTwistedArrowSource_isPrecompositionEquivalence _) a
  have h0 := dgTransportSquareFiberMap_ulift_isQCatEquivalence.{max (u + 1) v,
      max (u + 1) v + 1} p q f g hf b
    (dgHomTargetCosliceComparison_fibers_isQCatEquivalence R C x b)
  have h1 := dgTransportSquareFiberMap_ulift_isQCatEquivalence.{max (u + 1) v,
      max (u + 1) v + 1} q r f2 (𝟙 _) hf2' (g.app _ b) (hT (g.app _ b))
  have h2 := dgHomUnderlyingSpacePointedDisplay_fiber_isQCatEquivalence R C (g.app _ b)
  let U := SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}
  let W := dgHomUnderlyingSpacePointedDisplay R C
  let Ω := dgHomUnderlyingSpaceInfinity R C
  have hU0 : U.map f ≫ U.map q = U.map p ≫ U.map g := by
    rw [← Functor.map_comp, hf, Functor.map_comp]
  have hU1 : U.map f2 ≫ U.map r = U.map q ≫ U.map (𝟙 _) := by
    rw [← Functor.map_comp, hf2', Functor.map_comp]
  have hP : W ≫ pointedSpaceProjection = U.map r ≫ Ω :=
    dgHomUnderlyingSpacePointedDisplay_projection R C
  have hP1 : (U.map f2 ≫ W) ≫ pointedSpaceProjection =
      U.map q ≫ (U.map (𝟙 _) ≫ Ω) := by
    rw [Category.assoc, hP, ← Category.assoc, hU1, Category.assoc]
  have H12 : IsQCatEquivalence (transportSquareFiberMap (U.map q) pointedSpaceProjection
      (U.map f2 ≫ W) (U.map (𝟙 _) ≫ Ω) hP1 (ULift.up (g.app _ b))) := by
    rw [dgTransportSquareFiberMap_comp (U.map q) (U.map r) pointedSpaceProjection
      (U.map f2) (U.map (𝟙 _)) hU1 W Ω hP (ULift.up (g.app _ b))]
    exact h1.comp h2
  have hP0 : (U.map f ≫ (U.map f2 ≫ W)) ≫ pointedSpaceProjection =
      U.map p ≫ (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) := by
    rw [Category.assoc, hP1, ← Category.assoc, hU0, Category.assoc]
  have H : IsQCatEquivalence (transportSquareFiberMap (U.map p) pointedSpaceProjection
      (U.map f ≫ (U.map f2 ≫ W)) (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) hP0 (ULift.up b)) := by
    rw [dgTransportSquareFiberMap_comp (U.map p) (U.map q) pointedSpaceProjection
      (U.map f) (U.map g) hU0 (U.map f2 ≫ W) (U.map (𝟙 _) ≫ Ω) hP1 (ULift.up b)]
    exact h0.comp H12
  have hId : U.map (𝟙 (dgHomModuleNerve R C)) = 𝟙 (U.obj (dgHomModuleNerve R C)) :=
    U.map_id _
  have hF : U.map f ≫ (U.map f2 ≫ W) = dgHomTargetCoslicePointedDisplay R C x := rfl
  have hG : U.map g ≫ (U.map (𝟙 _) ≫ Ω) = dgHomTargetUnderlyingSpaceInfinity R C x := by
    erw [hId, Category.id_comp]
    rfl
  exact (dgTransportSquareFiberMap_congr (U.map p) pointedSpaceProjection
    (U.map f ≫ (U.map f2 ≫ W)) (dgHomTargetCoslicePointedDisplay R C x)
    (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) (dgHomTargetUnderlyingSpaceInfinity R C x)
    hF hG hP0 (dgHomTargetCoslicePointedDisplay_projection R C x) (ULift.up b)).mp H
end SerrePositivity.InfinityCategories
