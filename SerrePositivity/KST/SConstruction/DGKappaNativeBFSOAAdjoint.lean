module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOAComparison
public import SerrePositivity.KST.SConstruction.SOAExInfinityAdjointComparison
public import SerrePositivity.KST.SConstruction.PointedComponentAssemblyTransfer

/-!
概要：同じ有限 native BF と旧 SOA の正の構造随伴を成分で比較する。
方針：元の実 S₁ 比較と同じ組み立てを円柱四角形に接続する。
規約：全写像空間比較は行わない。使われ方：二頂点の実スペクトル弱比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra DifferentialGraded NonConnective
open Fibration Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
attribute [local instance] nativeFiniteStageKan nativeFiniteStepKan nativeFiniteBoundaryKan
  nativeFiniteStepLoopKan nativeFiniteAssemblySourceKan nativeFiniteBoundaryLoopKan

/-- 概要：同じ実次段の構造随伴は、元の左右脚の随伴四角形を成分で回収する。
方針：元の SOA 随伴と同じ実 BF 円柱の比較を合成する。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFStepAdjoint_component (r : ℕ)
    (S : DGKappaNativeBFFiniteStage.{u, v} R D I r) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    componentOf
        (((stableOneDirectionKanComparisonMap r C.obj).hom ≫
            (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
              (S.functor.obj C).obj from S.comparison C)) ≫
          curry (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
            ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj
            from dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C)) =
      componentOf (stableKanAssemblyRightAdjoint r C.obj ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj ⟶
            ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj
            from dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C)) := by
  have h := pointedEnrichedCylinderCompletion_component_square
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C
  erw [dgKappaNativeBFFiniteStepLeftMap_suspension.{u, v} R D I r S C] at h
  let l := (stableOneDirectionKanComparisonMap r C.obj).hom ≫
    (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
      (S.functor.obj C).obj from S.comparison C)
  let σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C
  let a : ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C).obj ⟶
      ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj :=
    dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r C
  let d : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C
  have hc := componentOf_curry h
  erw [curry_natural_left l σ, curry_natural_right a d] at hc
  exact hc

/-- 概要：元の一次方向商の SOA Kan 模型から同じ Ex∞ 模型への前向き比較。
方針：元の SOA 随伴と同じ実 BF 円柱の比較を合成する。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFSourceSOAComparison (r : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (oneDirectionKanRealizationFunctor r).obj
        (sInputModel C.obj) ⟶
      ((stableOneDirectionKanEnrichedFunctor r).obj C.obj).obj :=
  pointedSOAExInfinityComparison ((stableOneDirectionPointedEnrichedFunctor r).obj C.obj)

/-- 概要：元の随伴の SOA 延長と新 Ex∞ 随伴は、同じ前向き比較で点つき成分が可換。
方針：元の SOA 随伴と同じ実 BF 円柱の比較を合成する。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOAAssemblyAdjoint_component (r : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I)
    (w : (kanAssemblyAdjointChoices r
      (sInputModel C.obj)) _⦋0⦌) :
    componentOf (dgKappaNativeBFSourceSOAComparison.{u, v} R D I r C ≫
        stableKanAssemblyRightAdjoint r C.obj) =
      componentOf (kanAssemblyAdjointAt r
          (sInputModel C.obj) w ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (dgKappaNativeBFBoundarySOAComparison.{u, v} R D I (r + 1) C)) := by
  apply soaExInfinityAdjoint_component
    ((stableOneDirectionPointedEnrichedFunctor r).obj C.obj)
    ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj C.obj)
    ((oneDirectionAssemblyAdjointNat r).app
      (sInputModel C.obj))
  · exact kanAssemblyAdjointAt_fac r _ w
  · exact stableKanAssemblyRightAdjoint_unit r C.obj

/-- 概要：全正段の元の前向き比較は、旧・新構造随伴を点つき成分で結ぶ。
方針：元の SOA 随伴と同じ実 BF 円柱の比較を合成する。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFRawSOAComparison_positive_adjoint (r : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    componentOf (dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 1) ≫
        curry ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma (r + 1))) =
      componentOf (boundaryKanAssemblyAdjoint r
          (sInputModel C.obj) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 2))) := by
  let X : StableModel.{max (u + 1) v} := sInputModel C.obj
  let S := dgKappaNativeBFFinitePositiveStage.{u, v} R D I r
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}
  let q := (oneDirectionKanComparisonNat r).app X
  let g := oneDirectionKanComparisonInverse r X
  let α := dgKappaNativeBFSourceSOAComparison.{u, v} R D I r C
  let β := dgKappaNativeBFBoundarySOAComparison.{u, v} R D I r C
  let β' := dgKappaNativeBFBoundarySOAComparison.{u, v} R D I (r + 1) C
  let q' := (stableOneDirectionKanComparisonMap r C.obj).hom
  let c : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
      (S.functor.obj C).obj := S.comparison C
  let s : (S.functor.obj C).obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    curry (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj
      from dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I r S C)
  let d : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj ⟶
      ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj :=
    dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C
  let w := (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some
  let a := kanAssemblyAdjointAt r X w
  let a' := stableKanAssemblyRightAdjoint r C.obj
  have hi : componentOf (g ≫ q) = componentOf (𝟙 _) :=
    ((piZero_eq_iff_pointedHomotopy _ _).mpr
      (oneDirectionKanComparisonInverse_homotopy r X)).symm
  have hq : componentOf (α ≫ q') = componentOf (q ≫ β) :=
    pointedSOAExInfinityComparison_naturality_component
      (stableOneDirectionPointedComparisonMap r C.obj)
  have ha : componentOf (α ≫ a') = componentOf (a ≫ L.map β') :=
    dgKappaNativeBFSOAAssemblyAdjoint_component.{u, v} R D I r C w
  have hs : componentOf ((q' ≫ c) ≫ s) = componentOf (a' ≫ L.map d) :=
    dgKappaNativeBFStepAdjoint_component.{u, v} R D I r S C
  have ht := pointedComponentAssemblyTransfer q g α β q' c s a a'
    (L.map β') (L.map d) hi hq ha hs
  change componentOf ((β ≫ c) ≫ s) = componentOf ((g ≫ a) ≫ L.map (β' ≫ d))
  erw [L.map_comp]
  exact (congrArg componentOf (Category.assoc β c s)).trans ht

end SerrePositivity.KST.SConstruction
