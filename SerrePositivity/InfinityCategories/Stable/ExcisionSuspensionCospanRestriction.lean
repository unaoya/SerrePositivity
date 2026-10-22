module
public import SerrePositivity.InfinityCategories.Stable.ExcisionReplacementRestriction
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionFamily

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
namespace SerrePositivity.InfinityCategories

lemma excisionFullPunctured_upward {p q : ExcisionGridIndex.{u}} (hp : IsExcisionFullPunctured p)
    (h : p ≤ q) : IsExcisionFullPunctured q := hp.trans (Nat.add_le_add h.1 h.2)

lemma excisionGridSuspensionShape_source_le
    (v : (((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) _⦋0⦌) :
    nerveEquiv (excisionGridSquareEmbedding.app (Opposite.op ⦋0⦌) v.2) ≤
      nerveEquiv (excisionGridSuspensionShape.app (Opposite.op ⦋0⦌) v) := by
  rw [← excisionGridSuspensionEvaluateShape_source]
  change excisionGridSuspensionIndexMap.{u} ((0, 0),
    ((stdSimplex.objEquiv v.2.1).toOrderHom 0, (stdSimplex.objEquiv v.2.2).toOrderHom 0)) ≤
      excisionGridSuspensionIndexMap.{u}
        (((stdSimplex.objEquiv v.1.1).toOrderHom 0, (stdSimplex.objEquiv v.1.2).toOrderHom 0),
          ((stdSimplex.objEquiv v.2.1).toOrderHom 0, (stdSimplex.objEquiv v.2.2).toOrderHom 0))
  exact excisionGridSuspensionIndexMap.{u}.monotone ⟨⟨Fin.zero_le _, Fin.zero_le _⟩, le_rfl⟩

lemma excisionGridSuspensionCospan_noninitial
    (v : (((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (horn 2 2 : SSet.{u})) _⦋0⦌) :
    IsExcisionFullPunctured (nerveEquiv
      ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ cospanSquareBoundary ≫
        excisionGridSuspensionShape).app (Opposite.op ⦋0⦌) v)) := by
  have hp := (nerveEquiv
    (excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.2)).property
  have h := congrArg nerveEquiv (ConcreteCategory.congr_hom (NatTrans.congr_app
    excisionFullInputCospanBoundary_projection (Opposite.op ⦋0⦌)) v.2)
  change (nerveEquiv (excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.2)).val =
    nerveEquiv (excisionGridSquareEmbedding.app (Opposite.op ⦋0⦌)
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) v.2)) at h
  rw [h] at hp
  exact excisionFullPunctured_upward hp (excisionGridSuspensionShape_source_le
    (v.1, cospanSquareBoundary.app (Opposite.op ⦋0⦌) v.2))

lemma excisionRawSuspensionFamily_replaced_cospan {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :
    cospanSquareBoundary ≫ excisionRawSuspensionFamily (excisionReplaceInitial c) =
      cospanSquareBoundary ≫ excisionRawSuspensionFamily F := by
  apply uncurry_injective
  simp only [excisionRawSuspensionFamily, uncurry_natural_left, uncurry_curry]
  change ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ cospanSquareBoundary) ≫
    excisionGridSuspensionShape) ≫ excisionReplaceInitial c =
      ((((Δ[1] : SSet.{u}) ⊗ Δ[1]) ◁ cospanSquareBoundary) ≫
        excisionGridSuspensionShape) ≫ F
  exact excisionReplaceInitial_comp_of_noninitial c _ excisionGridSuspensionCospan_noninitial

end SerrePositivity.InfinityCategories
