module

public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverColimitCreation

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceCompactColimit
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction

/-!
概要：同じ全交互図式の余極限の存在から、両成分の余極限を比較する。
方針：全交互余極限を取り、両成分の cofinal 性と全余錐の一意性を使う。
規約：元の全図式の余極限の存在だけを使用する。
使われ方：底の slice 内で両成分の像を比較し、元の構造射との整合を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：同じ全交互図式の両 cofinal 成分の余極限頂点は同型。
方針：全交互余極限から同じ二つの制限余錐を回収して比較する。
規約：対象圏を任意に取り、固定標的の slice 内での適用も許す。
使われ方：相対交互構成の最終比較を底上の同型として得る。 -/
lemma alternatingColimit_vertexIso_of_hasColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingIndex κ)) ⟶ C)
    (hF : HasColimit F)
    (c₀ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 0)) ≫ F)) (hc₀ : IsColimitCone c₀)
    (c₁ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 1)) ≫ F)) (hc₁ : IsColimitCone c₁) :
    Nonempty (VertexIso c₀.vertex c₁.vertex) := by
  obtain ⟨c, hc⟩ := hF
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

/-- 概要：固定入力上の全交互図式の両成分余極限は、同じ入力の下の同型で比較できる。
方針：始点を持つ全交互形状の余極限を底から構成し、同じ全余極限から両成分を回収する。
規約：底の κ₀-filtered 余極限だけを要求する。
使われ方：元の入力を保持する compact 成分対の最終比較。 -/
lemma alternatingFixedSourceOverColimit_vertexIso
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    (hC : Ind.HasSmallKappaFilteredColimits κ C) (a : K ⟶ C)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ sliceUnder a}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingIndex κ)) ⟶ sliceOver x)
    (c₀ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 0)) ≫ F)) (hc₀ : IsColimitCone c₀)
    (c₁ : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ 1)) ≫ F)) (hc₁ : IsColimitCone c₁) :
    Nonempty (VertexIso c₀.vertex c₁.vertex) := by
  have := Cardinal.nonempty_ord_toType (c := κ) (Cardinal.IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  letI : OrderBot (AlternatingIndex κ) := {
    bot := toLex (⊥, 0)
    bot_le b := Prod.Lex.le_iff.mpr (by
      rcases (bot_le : (⊥ : κ.ord.ToType) ≤ (ofLex b).1).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Fin.zero_le _⟩) }
  have : IsCardinalFiltered (AlternatingIndex κ) κ := alternatingIndex_isCardinalFiltered κ
  have : IsKappaFiltered κ (nerve (AlternatingIndex κ)) :=
    Ind.isKappaFiltered_nerve_of_cardinalFiltered _
  have hF : HasColimit F := sliceOver_hasColimit_of_projection x F
    (fixedSource_orderBot_hasColimit a (AlternatingIndex κ) (F ≫ sliceOverProjection x)
      (hC (nerve (AlternatingIndex κ))
        (F ≫ sliceOverProjection x ≫ sliceUnderProjection a)))
  exact alternatingColimit_vertexIso_of_hasColimit κ F hF c₀ hc₀ c₁ hc₁

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
