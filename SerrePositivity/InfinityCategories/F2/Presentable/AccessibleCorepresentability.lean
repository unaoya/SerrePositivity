module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndCorepresentability
public import SerrePositivity.InfinityCategories.F2.Presentable.CorepresentabilityEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.IndCardinalChange
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceSmallLimits

/-!
概要：小極限を持つ accessible 圏の accessible な極限保存関手の余表現可能性。
方針：関手と圏の濃度をそろえ、Ind 模型上の全自然な retract を分裂して元へ移す。
規約：余表現対象と比較同型の存在を追加仮定にしない。
使われ方：HTT 5.5.2.7 と presentable 圏の随伴関手定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：accessible な小極限保存関手は元の accessible かつ完備な圏の対象で余表現可能。
方針：同じ濃度の Ind 模型へ引き戻し、構成した余表現対象を全同値で送る。
規約：小極限の存在と保存は元の宇宙の全錐について要求する。
使われ方：左随伴の存在に必要な空間値関手の余表現可能性。 -/
lemma accessible_preservesLimits_isCorepresentable
    {C : SSet.{u + 1}} [Quasicategory C] (F : C ⟶ SpaceInfinity.{u})
    (hCa : IsAccessible C) (hCl : HasSmallLimits C)
    (hFa : IsAccessibleFunctor F) (hFl : PreservesSmallLimits F) :
    IsCorepresentableSmallSpaceFunctor F := by
  obtain ⟨μ, _, hμF⟩ := hFa
  obtain ⟨κ, hμκ, hκC⟩ := hCa.exists_larger μ
  have : Fact κ.IsRegular := ⟨hκC.1⟩
  obtain ⟨A, hA, i, e, _, he, _⟩ := hκC.exists_indRepresentation
  have := hA
  have hκF : IsKappaAccessibleFunctor κ F := hμF.of_le hμκ.le
  have hF' : IsKappaAccessibleFunctor κ (e.hom ≫ F) := he.comp hκF
  have hC' : HasSmallLimits (Ind.IndInfinity κ A) := hCl.of_equivalence e.symm
  have hl' : PreservesSmallLimits (e.hom ≫ F) := by
    intro K D c hc
    have h := hFl K (D ≫ e.hom) (mapJoinCone e.hom c) ((e.isLimitCone_iff c).mp hc)
    exact (F2.isLimitCone_iff_of_cone_val_eq
      (mapJoinCone (e.hom ≫ F) c) (mapJoinCone F (mapJoinCone e.hom c))
      (Category.assoc c.val e.hom F).symm).mpr h
  exact isCorepresentable_of_equivalence_restriction e F
    (ind_corepresentable_of_continuous_preservesLimits κ A hC' (e.hom ≫ F) hF' hl')

end SerrePositivity.InfinityCategories.F2.Presentable
