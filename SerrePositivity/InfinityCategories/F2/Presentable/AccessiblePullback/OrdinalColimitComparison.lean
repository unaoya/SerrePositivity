module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.OrdinalCompactColimits
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction

/-!
概要：長さ κ₀ の同じ全交互図式の両成分の余極限頂点を同型で比較する。
方針：全交互余極限を取り、両成分の cofinal 性と全余錐の一意性を使う。
規約：κ₀-filtered 余極限の存在だけを使用する。
使われ方：底の slice 内で両成分の像を比較し、元の構造射との整合を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：同じ全交互図式の両 cofinal 成分の余極限頂点は同型。
方針：全交互余極限から同じ二つの制限余錐を回収して比較する。
規約：対象圏を任意に取り、固定標的の slice 内での適用も許す。
使われ方：相対交互構成の最終比較を底上の同型として得る。 -/
lemma alternatingColimit_vertexIso (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingIndex κ)) ⟶ C)
    (c₀ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 0)) ≫ F)) (hc₀ : IsColimitCone c₀)
    (c₁ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 1)) ≫ F)) (hc₁ : IsColimitCone c₁) :
    Nonempty (VertexIso c₀.vertex c₁.vertex) := by
  have : IsCardinalFiltered (AlternatingIndex κ) κ := alternatingIndex_isCardinalFiltered κ
  have : IsKappaFiltered κ (nerve (AlternatingIndex κ)) :=
    Ind.isKappaFiltered_nerve_of_cardinalFiltered _
  obtain ⟨c, hc⟩ := hC (nerve (AlternatingIndex κ)) F
  let s₀ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingSection κ 0))
  let s₁ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingSection κ 1))
  have h₀ : IsColimitCone (c.restrict s₀) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal s₀
      (Ind.isRightCofinal_ulift _ (alternatingSection_isRightCofinal κ 0)) c).mp hc
  have h₁ : IsColimitCone (c.restrict s₁) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal s₁
      (Ind.isRightCofinal_ulift _ (alternatingSection_isRightCofinal κ 1)) c).mp hc
  have e₀ : VertexIso c₀.vertex c.vertex := by
    simpa only [JoinCocone.vertex_restrict] using
      (colimitVertexIso c₀ (c.restrict s₀) hc₀ h₀)
  have e₁ : VertexIso c₁.vertex c.vertex := by
    simpa only [JoinCocone.vertex_restrict] using
      (colimitVertexIso c₁ (c.restrict s₁) hc₁ h₁)
  exact ⟨e₀ ≪≫ e₁.symm⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
