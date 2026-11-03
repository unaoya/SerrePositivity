module
public import SerrePositivity.InfinityCategories.Stable.ExcisionInitialReplacement
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionFullJoinIso_squareCone
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridIndex.{u})
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve ExcisionFullPuncturedIndex.{u})
    (hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
      cospanSquareBoundary ≫ Q)
    (hQ : squareVertex Q 0 0 = nerveVertex excisionGridInitialPoint) :
    cospanConeSquareIso.hom ≫ Q = joinMap (𝟙 Δ[0]) b ≫ excisionFullJoinIso.hom := by
  let d : JoinCone (pullbackCospan Q) := ⟨joinMap (𝟙 Δ[0]) b ≫
    excisionFullJoinIso.hom, by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc, excisionFullJoinIso_inr]
      exact hb⟩
  have hd : d.vertex = nerveVertex excisionGridInitialPoint := by
    rw [JoinCone.vertex_eq]
    change SSet.yonedaEquiv (joinInl Δ[0] (horn 2 2 : SSet.{u}) ≫
      (joinMap (𝟙 Δ[0]) b ≫ excisionFullJoinIso.hom)) = _
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp, excisionFullJoinIso_inl]
    rfl
  exact thinNerveCone_val_eq_of_vertex (pullbackCone Q) d rfl
    (by rw [pullbackCone_vertex, hQ, hd])

lemma excisionReplaceInitial_squareCone_val {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridIndex.{u})
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve ExcisionFullPuncturedIndex.{u})
    (hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
      cospanSquareBoundary ≫ Q)
    (hQ : squareVertex Q 0 0 = nerveVertex excisionGridInitialPoint) :
    (pullbackCone (Q ≫ excisionReplaceInitial c)).val =
      (restrictJoinCone c b).val := by
  have h := congrArg (fun q ↦ q ≫ excisionFullJoinIso.{u}.inv)
    (excisionFullJoinIso_squareCone Q b hb hQ)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  change cospanConeSquareIso.hom ≫ (Q ≫ (excisionFullJoinIso.inv ≫ c.val)) =
    joinMap (𝟙 Δ[0]) b ≫ c.val
  simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ c.val) h

lemma excisionReplaceInitial_isPullback_iff {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridIndex.{u})
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve ExcisionFullPuncturedIndex.{u})
    (hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
      cospanSquareBoundary ≫ Q)
    (hQ : squareVertex Q 0 0 = nerveVertex excisionGridInitialPoint) :
    IsPullbackSquare (Q ≫ excisionReplaceInitial c) ↔
      IsLimitCone (restrictJoinCone c b) :=
  F2.isLimitCone_iff_of_cone_val_eq _ _
    (excisionReplaceInitial_squareCone_val c Q b hb hQ)

end SerrePositivity.InfinityCategories
