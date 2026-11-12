module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTransportSquareFiberUniverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetCosliceFiberEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C)
/-- 同じ実 Hom 単位による持ち上げた pointed 表示の全ての実 fiber 射は全空間同値。 -/
lemma dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))))
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_projection R C x) (ULift.up b)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C))
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison R C x
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x)
  let f2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)
  have hf : f ≫ q = p ≫ g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison_projection R C x
  have hf2 : f2 ≫ r = q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection _
  have hf2' : f2 ≫ r = q ≫ 𝟙 _ := hf2.trans (Category.comp_id q).symm
  have hT (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R C) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap q r f2 (𝟙 _) hf2' a) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence q r f2 hf2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isPrecompositionEquivalence _) a
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_ulift_isQCatEquivalence.{max (u + 1) v,
      max (u + 1) v + 1} p q f g hf b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison_fibers_isQCatEquivalence R C x b)
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_ulift_isQCatEquivalence.{max (u + 1) v,
      max (u + 1) v + 1} q r f2 (𝟙 _) hf2' (g.app _ b) (hT (g.app _ b))
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpacePointedDisplay_fiber_isQCatEquivalence R C (g.app _ b)
  let U := SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}
  let W := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpacePointedDisplay R C
  let Ω := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C
  have hU0 : U.map f ≫ U.map q = U.map p ≫ U.map g := by
    rw [← Functor.map_comp, hf, Functor.map_comp]
  have hU1 : U.map f2 ≫ U.map r = U.map q ≫ U.map (𝟙 _) := by
    rw [← Functor.map_comp, hf2', Functor.map_comp]
  have hP : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = U.map r ≫ Ω :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpacePointedDisplay_projection R C
  have hP1 : (U.map f2 ≫ W) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      U.map q ≫ (U.map (𝟙 _) ≫ Ω) := by
    rw [Category.assoc, hP, ← Category.assoc, hU1, Category.assoc]
  have H12 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap (U.map q) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f2 ≫ W) (U.map (𝟙 _) ≫ Ω) hP1 (ULift.up (g.app _ b))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_comp (U.map q) (U.map r) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f2) (U.map (𝟙 _)) hU1 W Ω hP (ULift.up (g.app _ b))]
    exact h1.comp h2
  have hP0 : (U.map f ≫ (U.map f2 ≫ W)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      U.map p ≫ (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) := by
    rw [Category.assoc, hP1, ← Category.assoc, hU0, Category.assoc]
  have H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap (U.map p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f ≫ (U.map f2 ≫ W)) (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) hP0 (ULift.up b)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_comp (U.map p) (U.map q) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (U.map f) (U.map g) hU0 (U.map f2 ≫ W) (U.map (𝟙 _) ≫ Ω) hP1 (ULift.up b)]
    exact h0.comp H12
  have hId : U.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R C)) = 𝟙 (U.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R C)) :=
    U.map_id _
  have hF : U.map f ≫ (U.map f2 ≫ W) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x := rfl
  have hG : U.map g ≫ (U.map (𝟙 _) ≫ Ω) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x := by
    erw [hId, Category.id_comp]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTransportSquareFiberMap_congr (U.map p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (U.map f ≫ (U.map f2 ≫ W)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x)
    (U.map g ≫ (U.map (𝟙 _) ≫ Ω)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
    hF hG hP0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_projection R C x) (ULift.up b)).mp H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
