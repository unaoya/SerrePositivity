module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionReplacementRestriction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionFamily

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionFullPunctured_upward {p q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}} (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured p)
    (h : p ≤ q) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured q := hp.trans (Nat.add_le_add h.1 h.2)

lemma excisionGridSuspensionShape_source_le
    (v : (((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) _⦋0⦌) :
    nerveEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding.app (Opposite.op ⦋0⦌) v.2) ≤
      nerveEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape.app (Opposite.op ⦋0⦌) v) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape_source]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionIndexMap.{u} ((0, 0),
    ((stdSimplex.objEquiv v.2.1).toOrderHom 0, (stdSimplex.objEquiv v.2.2).toOrderHom 0)) ≤
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionIndexMap.{u}
        (((stdSimplex.objEquiv v.1.1).toOrderHom 0, (stdSimplex.objEquiv v.1.2).toOrderHom 0),
          ((stdSimplex.objEquiv v.2.1).toOrderHom 0, (stdSimplex.objEquiv v.2.2).toOrderHom 0))
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionIndexMap.{u}.monotone ⟨⟨Fin.zero_le _, Fin.zero_le _⟩, le_rfl⟩

lemma excisionGridSuspensionCospan_noninitial
    (v : (((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (horn 2 2 : SSet.{u})) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured (nerveEquiv
      ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape).app (Opposite.op ⦋0⦌) v)) := by
  have hp := (nerveEquiv
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.2)).property
  have h := congrArg nerveEquiv (ConcreteCategory.congr_hom (NatTrans.congr_app
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary_projection (Opposite.op ⦋0⦌)) v.2)
  change (nerveEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.2)).val =
    nerveEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) v.2)) at h
  rw [h] at hp
  exact excisionFullPunctured_upward hp (excisionGridSuspensionShape_source_le
    (v.1, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) v.2))

lemma excisionRawSuspensionFamily_replaced_cospan {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily F := by
  apply uncurry_injective
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily, uncurry_natural_left, uncurry_curry]
  change ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c =
      ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape) ≫ F
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_comp_of_noninitial c _ excisionGridSuspensionCospan_noninitial

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
