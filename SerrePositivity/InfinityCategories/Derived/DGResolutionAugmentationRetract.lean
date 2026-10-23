module
public import SerrePositivity.InfinityCategories.Derived.DGResolvedProjectiveVertex
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLocalization
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulIsoRecovery
/-!
概要：同じ分解 augmentation の半自由入力制限から、元の円柱を保持した戻り同型を回収する。
方針：各半自由入力の射影性と、実半自由包含の完全充満性を使う。
規約：既存の指定導来単位は変更しない。使われ方：K-flat の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の分解 augmentation を半自由入力に制限し、同じ円柱を保って端点を揃える。 -/
def dgModuleResolutionSemifreeAugmentationHomotopy :
    SSet.Homotopy
      ((dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)) ≫
        dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D))) ≫
          dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
            (dgModuleSemifreeProperty R D)))
      ((𝟙 (dgModuleDerivedInfinityCategory R D)) ≫
        dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D))) := by
  let H := functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R D)
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleSemifreeProperty R D)))
  exact { h := H.h
          h₀ := by simpa only [Category.assoc] using! H.h₀
          h₁ := by simpa only [Category.comp_id, Category.id_comp] using! H.h₁
          rel := H.rel }
/-- 半自由入力上では同じ augmentation の各実頂点辺が可逆。 -/
lemma dgModuleResolutionSemifreeAugmentationHomotopy_vertex_isInvertible
    (x : (dgModuleDerivedInfinityCategory R D) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleResolutionSemifreeAugmentationHomotopy R D) x).toTruncated := by
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := SemifreeDGModules R D)).symm.surjective x
  have hr := dgModuleResolvedAugmentationHomotopy_projective_vertex_isInvertible
    R (RightModule R D) D (DGFunctor.id (RightModule R D)) M.val
    (dgSemifreeModule_isProjective R D M)
  have hh : (simplicialHomotopyVertexEdge (dgModuleResolutionSemifreeAugmentationHomotopy R D)
      (Simplex.vertex M)).edge =
      (simplicialHomotopyVertexEdge (dgModuleResolutionAugmentationHomotopy R D)
        (Simplex.vertex M.val)).edge := by
    exact simplicialHomotopyVertexEdge_precomp_edge _ _ _
  exact (isInvertibleEdge_congr hh).mpr ((isInvertibleEdge_congr rfl).mpr hr)
/-- 同じ augmentation の半自由制限から回収した分解の戻り同型。 -/
def dgModuleResolutionAugmentationRetractIso :
    FunctorIso
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleSemifreeProperty R D)) ≫
        dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D)))
      (𝟙 (dgModuleDerivedInfinityCategory R D)) :=
  (dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (functorIsoOfPointwiseInvertibleHomotopy (dgModuleResolutionSemifreeAugmentationHomotopy R D)
      (dgModuleResolutionSemifreeAugmentationHomotopy_vertex_isInvertible R D))
/-- 回収した戻り同型の実包含後の射は、同じ半自由制限円柱の類。 -/
lemma dgModuleResolutionAugmentationRetractIso_postcomp_hom :
    ((dgModuleResolutionAugmentationRetractIso R D).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))).hom =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgModuleResolutionSemifreeAugmentationHomotopy R D)) := by
  unfold dgModuleResolutionAugmentationRetractIso
  rw [(dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso_postcomp]
  rfl
end SerrePositivity.InfinityCategories
