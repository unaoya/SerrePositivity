module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.VertexProjector
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DeformationRetract
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.NativeVertexModuleMaps

/-!
# 補正包含を通した同じ native 頂点列

## 概要
native 頂点列と補正包含の合成は、元の零 shift 包含の同じ成分である。

## 方針
零次元層の既存の式を使い、射影・補正包含の合成を安定自己射へ戻す。

## 規約
零 shift 同型を消去せず、厳密な射の成分として保持する。

## 使われ方
HA 1.2.4。元の標準脚と指定余錐の脚の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet SerrePositivity.DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open StrictComparison
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

/-- 同じ native 頂点列を補正包含へ送ると、零 shift の元の余積包含となる。 -/
theorem dgBarNativeVertexModuleMap_inclusion_f (s : I _⦋0⦌) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgBarNativeVertexModuleMap R D F s ≫
      dgCoherentBarNormalizedModuleInclusionUnconditional R D F)).f q =
    ((moduleEvaluation R D x).map
      (moduleShiftZeroIsoObj R D (dgCoherentBarSource R D F ⟨0, s⟩)).inv).f q ≫
      ((moduleEvaluation R D x).map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q := by
  let E := moduleEvaluation R D x
  let σ := moduleShiftZeroIsoObj R D (dgCoherentBarSource R D F ⟨0, s⟩)
  let p := dgCoherentBarNormalizedModuleProjectionUnconditional R D F
  let i := dgCoherentBarNormalizedModuleInclusionUnconditional R D F
  have hv := congrArg (fun f => (E.map f).f q) (dgBarZeroLayerInclusion_ι R D F s)
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hv
  have hz := dgBarZeroLayerInclusion_column_f R D F s x q
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hz
  have hp := dgCoherentBarNormalizedModuleProjection_evaluation_f R D F
    (dgCoherentBarMaurerCartan_unconditional R D F) x q
  have hσ := congrArg (fun f => (E.map f).f q) σ.inv_hom_id
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hσ
  have hi := E.map_id (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F ⟨0, s⟩))
  rw [hi, HomologicalComplex.id_f] at hσ
  have hc : (E.map σ.hom).f q ≫ (E.map (dgBarNativeVertexModuleMap R D F s)).f q =
      (E.map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q ≫ (E.map p).f q := by
    have h := hv.symm.trans hz
    change _ = _ ≫ ((moduleEvaluation R D x).map
      (dgCoherentBarNormalizedProjection R D F)).f q at h
    rw [← hp] at h
    exact h
  have hn : (E.map (dgBarNativeVertexModuleMap R D F s)).f q =
      (E.map σ.inv).f q ≫ ((E.map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q ≫
        (E.map p).f q) := by
    calc
      _ = ((E.map σ.inv).f q ≫ (E.map σ.hom).f q) ≫
          (E.map (dgBarNativeVertexModuleMap R D F s)).f q := by rw [hσ, Category.id_comp]
      _ = _ := by rw [Category.assoc, hc]
  rw [Functor.map_comp, HomologicalComplex.comp_f]
  change (E.map (dgBarNativeVertexModuleMap R D F s)).f q ≫ (E.map i).f q = _
  rw [hn]
  simp only [Category.assoc]
  change (E.map σ.inv).f q ≫ (E.map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q ≫
    ((E.map p).f q ≫ (E.map i).f q) = _
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    dgCoherentBarNormalizedModuleProjectionUnconditional_inclusion R D F]
  rw [dgCoherentBarNormalizationEndomorphism_vertex_f R D F
    (dgCoherentBarMaurerCartan_unconditional R D F) s x q]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
