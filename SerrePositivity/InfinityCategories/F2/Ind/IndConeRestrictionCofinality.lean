module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeRestrictionUnderCocone
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Core.InnerPullback
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramCommaEvaluation

/-!
概要：下方 comma が κ-filtered なら、元の余錐図式から下方図式への制限は right cofinal。
方針：指定全変換下の実余錐で under 引き戻しを filtered とし、元の点で Quillen A を使う。
規約：元の制限写像と全評価写像を保持し、追加の Kan 性やモデル圏仮定を要求しない。
使われ方：有限半順序図式の旧頂点評価の共終性を点追加の前後で伝播する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join K (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
  (hK : IsKappaSmall κ K)
  (hLower : IsKappaFiltered κ (smallDiagramComma κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D)))
include hK hLower
/-- 概要：元の下方制限の指定図式下の実 under comma は filtered。
方針：全ての小さい試験族の実余錐を使う。規約：元の全族。使われ方：Quillen A の入力。 -/
lemma indConeRestrictionComma_isFiltered {B : SSet.{u}} (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ diagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D)) :
    IsFilteredInfinity (pullback (sliceUnderProjection z)
      (diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u})))) := by
  apply isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  exact nonempty_indConeRestrictionComma_cocone κ D hK hLower hA hB z q
/-- 概要：元の余錐図式 comma から元の下方図式 comma への制限は right cofinal。
方針：元の点の under comma の弱可縮性。規約：同じ制限写像。使われ方：旧評価の共終性。 -/
lemma diagramCommaRestriction_cone_inl_isRightCofinal :
    IsRightCofinal (diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u}))) := by
  apply isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have := indConeRestrictionComma_isFiltered κ D hK hLower
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le (Δ[0] : SSet.{u})) z
  exact isWeaklyContractible_of_isFilteredInfinity _
/-- 概要：元の下方の指定頂点評価の共終性は、元の同じ余錐図式の評価に伝わる。
方針：元の制限と評価の厳密な合成則。規約：元の指定値。使われ方：有限形状の点追加。 -/
lemma diagramCommaEvaluation_cone_inl_isRightCofinal (k : K _⦋0⦌)
    (hk : IsRightCofinal (diagramCommaEvaluation κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D) k)) :
    IsRightCofinal (diagramCommaEvaluation κ D
      ((joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) k)) := by
  rw [← diagramCommaRestriction_evaluate κ D (joinInl K (Δ[0] : SSet.{u})) k]
  exact (diagramCommaRestriction_cone_inl_isRightCofinal κ D hK hLower).comp hk
/-- 概要：同じ小さい表示添字からの元の旧頂点評価も right cofinal。
方針：元の小さい模型の同型を合成。規約：同じ全評価写像。使われ方：単一 filtered 表示。 -/
lemma smallDiagramCommaEvaluation_cone_inl_isRightCofinal (k : K _⦋0⦌)
    (hk : IsRightCofinal (diagramCommaEvaluation κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D) k)) :
    IsRightCofinal (smallDiagramCommaEvaluation κ D
      ((joinInl K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) k)) :=
  (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_cone_inl_isRightCofinal κ D hK hLower k hk)
end SerrePositivity.InfinityCategories.F2.Ind
