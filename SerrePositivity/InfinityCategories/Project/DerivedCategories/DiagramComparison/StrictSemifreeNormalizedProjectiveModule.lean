module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeNormalizedBarRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeProjectiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectiveComplexEvaluationComparison

/-!
概要：元の正規化barの同じ通常関手を射影的一点加群へ制限する。
方針：既存の正規化barの射影性と充満包含のpreimageを使う。
規約：元の正規化加群と全自然変換を保持する。
使われ方：3b-3 R6 U39、照合C2・C3の証明分割。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U39の包装：同じ正規化barの全射を射影的一点加群へ制限する。 -/
def strictSemifreeNormalizedProjectiveModule :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤
      ClosedCategory A (ProjectiveDGModules A PUnit.{1}) where
  obj F := ForgetEnrichment.of (Complex A)
    ⟨ForgetEnrichment.to (Complex A)
      ((strictBarNormalizedFunctor A SimplexCategoryᵒᵖ).obj
        ((strictSemifreePointUnderlyingFunctor A).obj F)),
      strictBarNormalizedFunctor_projective A SimplexCategoryᵒᵖ _
        (strictSemifreePointUnderlyingFunctor_projective A F)⟩
  map f := (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleProjectiveProperty A PUnit.{1})).onClosed.preimage
      ((strictSemifreePointUnderlyingFunctor A ⋙
        strictBarNormalizedFunctor A SimplexCategoryᵒᵖ).map f)
  map_id F := by
    apply (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})).onClosed.map_injective
    rw [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})).onClosed.map_injective
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]

/-- 同じ全射影的模型の包含は、元の正規化barの全関手を復元する。 -/
lemma strictSemifreeNormalizedProjectiveModule_underlying :
    strictSemifreeNormalizedProjectiveModule A ⋙
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleProjectiveProperty A PUnit.{1})).onClosed =
      strictSemifreePointUnderlyingFunctor A ⋙ strictBarNormalizedFunctor A SimplexCategoryᵒᵖ := by
  apply CategoryTheory.Functor.hext
  · intro F
    rfl
  · intro F G f
    apply heq_of_eq
    exact (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})).onClosed.map_preimage _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
