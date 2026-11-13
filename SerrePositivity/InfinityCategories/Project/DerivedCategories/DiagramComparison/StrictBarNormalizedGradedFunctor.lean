module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarGradedFunctor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedGraded

/-!
概要：非退化射列のbarのgraded直和も元の自然変換に関手的にし、同じ射影と包含を照合する。
方針：同じ添字集合上で先頭の成分をシフトし、退化・非退化の分岐を保つ。
規約：まだMC微分との可換性やnative余錐の自然性は主張しない。
使われ方：3b-3 R6、正規化barの全パラメーター比較の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 非退化の元の各射列の先頭の成分を、同じシフトで写す。 -/
def strictBarNormalizedGradedMap {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F) ⟶
      dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A G) :=
  Sigma.desc (fun s =>
    (moduleShiftFunctor A PUnit.{1} (s.val.1 : ℤ)).map (η.app (s.val.2.down.obj 0)) ≫
      Sigma.ι (dgCoherentBarNormalizedFamily A PUnit.{1} (smallStrictBarDiagram A G)) s)

/-- 同じ非退化因子での像は、元の同じシフトした自然変換成分。 -/
@[reassoc]
lemma strictBarNormalizedGradedMap_ι {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G)
    (s : dgCoherentBarNormalizedIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    Sigma.ι (dgCoherentBarNormalizedFamily A PUnit.{1} (smallStrictBarDiagram A F)) s ≫
        strictBarNormalizedGradedMap A J η =
      (moduleShiftFunctor A PUnit.{1} (s.val.1 : ℤ)).map (η.app (s.val.2.down.obj 0)) ≫
        Sigma.ι (dgCoherentBarNormalizedFamily A PUnit.{1} (smallStrictBarDiagram A G)) s :=
  Sigma.ι_comp_desc _ _

/-- 非退化ラベルの同じgraded barの通常関手。 -/
def strictBarNormalizedGradedFunctor :
    (J ⥤ ModuleCategory A PUnit.{1}) ⥤ ModuleCategory A PUnit.{1} where
  obj F := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)
  map η := strictBarNormalizedGradedMap A J η
  map_id F := by
    apply Sigma.hom_ext
    intro s
    rw [strictBarNormalizedGradedMap_ι]
    simp
  map_comp η θ := by
    apply Sigma.hom_ext
    intro s
    rw [strictBarNormalizedGradedMap_ι, strictBarNormalizedGradedMap_ι_assoc,
      strictBarNormalizedGradedMap_ι]
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]

/-- 非退化因子の元の包含は、元の図式の自然変換に厳密に自然。 -/
lemma strictBarNormalizedGradedMap_inclusion
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    strictBarNormalizedGradedMap A J η ≫
        dgCoherentBarNormalizedInclusion A PUnit.{1} (smallStrictBarDiagram A G) =
      dgCoherentBarNormalizedInclusion A PUnit.{1} (smallStrictBarDiagram A F) ≫
        strictBarGradedMap A J η := by
  apply Sigma.hom_ext
  intro s
  rw [strictBarNormalizedGradedMap_ι_assoc, dgCoherentBarNormalizedInclusion_ι_assoc,
    strictBarGradedMap_ι, dgCoherentBarNormalizedInclusion_ι]

/-- 退化因子を殺す元の同じ射影も、元の図式の自然変換に厳密に自然。 -/
lemma strictBarGradedMap_projection
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    strictBarGradedMap A J η ≫
        dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A G) =
      dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A F) ≫
        strictBarNormalizedGradedMap A J η := by
  classical
  apply Sigma.hom_ext
  intro s
  by_cases hs : s.2 ∈ ((SSet.uliftFunctor.{u, 0}).obj (nerve J)).nonDegenerate s.1
  · let t : dgCoherentBarNormalizedIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) := ⟨s, hs⟩
    change Sigma.ι _ t.val ≫ _ = Sigma.ι _ t.val ≫ _
    rw [strictBarGradedMap_ι_assoc, dgCoherentBarNormalizedProjection_ι_assoc,
      strictBarNormalizedGradedMap_ι, dgCoherentBarNormalizedProjection_ι]
  · have hd : s.2 ∈ ((SSet.uliftFunctor.{u, 0}).obj (nerve J)).degenerate s.1 := by
      change ¬¬ s.2 ∈ ((SSet.uliftFunctor.{u, 0}).obj (nerve J)).degenerate s.1 at hs
      exact Classical.not_not.mp hs
    let t : dgCoherentBarDegenerateIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) := ⟨s, hd⟩
    change Sigma.ι _ t.val ≫ _ = Sigma.ι _ t.val ≫ _
    rw [strictBarGradedMap_ι_assoc, dgCoherentBarNormalizedProjection_ι_degenerate_assoc,
      dgCoherentBarNormalizedProjection_ι_degenerate]
    simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
