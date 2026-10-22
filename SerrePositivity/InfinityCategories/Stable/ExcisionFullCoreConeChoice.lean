module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedCones
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePuncturedLimitCone
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionParameters
public import SerrePositivity.InfinityCategories.Stable.ExcisionInitialReplacementSquare

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionFullCorePunctured_base {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    nerveMap excisionCorePuncturedToFull.toFunctor ≫
      (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F) =
    nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F) := by
  rw [← Category.assoc, excisionCorePuncturedToFull_projection]
  simp only [Category.assoc]

lemma exists_excisionFullLimitCone_of_core {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)))
    (hc : IsLimitCone c) :
    ∃ d : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F),
      IsLimitCone d ∧
      (F2.restrictJoinCone d (nerveMap excisionCorePuncturedToFull.toFunctor)).val = c.val ∧
      d.vertex = c.vertex := by
  let c' : JoinCone (nerveMap excisionCorePuncturedToFull.toFunctor ≫
      (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :=
    ⟨c.val, c.property.trans (excisionFullCorePunctured_base F).symm⟩
  have hc' : IsLimitCone c' := (F2.isLimitCone_iff_of_cone_val_eq c c' rfl).mp hc
  obtain ⟨d, hd, hr, hv⟩ := excisionFullPunctured_limitCone_extension _ c' hc'
  refine ⟨d, hd, ?_, hv⟩
  exact congrArg Subtype.val hr

lemma exists_excisionFullLimitCone_of_input {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)) 2 2)))
    (hd : IsLimitCone d) :
    ∃ c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F),
      IsLimitCone c ∧
      (F2.restrictJoinCone c (nerveMap excisionCorePuncturedToFull.toFunctor)).val =
        (excisionCorePuncturedLimitCone
          (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)
          d hd).val ∧ c.vertex = d.vertex := by
  let G := nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F
  obtain ⟨c, hc, hr, hv⟩ := exists_excisionFullLimitCone_of_core F
    (excisionCorePuncturedLimitCone G d hd) (excisionCorePuncturedLimitCone_isLimit G d hd)
  exact ⟨c, hc, hr, hv.trans (excisionCorePuncturedLimitCone_vertex G d hd)⟩

lemma excisionReplaceInitial_coreOuterCone_val {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (d : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫
      (nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫ F)))
    (hr : (F2.restrictJoinCone c (nerveMap excisionCorePuncturedToFull.toFunctor)).val =
      d.val) :
    (pullbackCone (excisionGridSuspensionAt 0 0 ≫ excisionReplaceInitial c)).val =
      (excisionCorePuncturedOuterCone d).val := by
  let b := excisionCoreOuterCospanBoundary ≫ nerveMap excisionCorePuncturedToFull.toFunctor
  have hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
      cospanSquareBoundary ≫ excisionGridSuspensionAt 0 0 := by
    dsimp only [b]
    rw [Category.assoc, excisionCorePuncturedToFull_projection,
      excisionGridSuspensionAt_source]
    simp only [← Category.assoc, excisionCoreOuterCospanBoundary_projection]
  have hQ : squareVertex (excisionGridSuspensionAt.{u} 0 0) 0 0 =
      nerveVertex excisionGridInitialPoint := by rfl
  rw [excisionReplaceInitial_squareCone_val c _ b hb hQ]
  change joinMap (𝟙 Δ[0]) b ≫ c.val = joinMap (𝟙 Δ[0]) excisionCoreOuterCospanBoundary ≫ d.val
  dsimp only [b]
  rw [← Category.id_comp (𝟙 (Δ[0] : SSet.{u})), joinMap_comp, Category.assoc]
  exact congrArg (fun q ↦ joinMap (𝟙 Δ[0]) excisionCoreOuterCospanBoundary ≫ q) hr

end SerrePositivity.InfinityCategories
