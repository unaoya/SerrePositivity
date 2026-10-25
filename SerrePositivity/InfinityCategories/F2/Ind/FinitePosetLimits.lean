module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitFromPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetDiagramPresentation
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：有限半順序形状の Ind 極限の存在と、同じ全錐の包含による保存・反映。
方針：元の図式の単一 filtered 表示を全極限錐族へ拡張し、同じ錐の一意性を使う。
規約：一般有限交換は明示入力。任意の有限単体集合形状への一般化は別工程。
使われ方：Ind の引き戻しの存在と安定性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
  (hex : IndFiniteLimitExchangeInput.{u}) {P : Type u} [PartialOrder P] [Finite P]
  {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)

include hκ hex

/-- 元の有限半順序図式の極限全錐があり、元の前層への包含もその同じ錐を保存する。 -/
lemma indFinitePoset_exists_limitCone : ∃ c : JoinCone D,
    IsLimitCone c ∧ IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) :=
  ind_exists_limitCone_of_singleFilteredDiagramPresentation κ hκ hex D
    (indFinitePoset_has_singleFilteredDiagramPresentation κ D)

/-- 明示交換入力のもとで、元の有限半順序全図式は極限を持つ。 -/
lemma indFinitePoset_hasLimit : HasLimit D := by
  obtain ⟨c, hc, _⟩ := indFinitePoset_exists_limitCone κ hκ hex D
  exact ⟨c, hc⟩

/-- 同じ包含は元の有限半順序極限の任意の指定全錐を保存する。 -/
lemma indFinitePoset_inclusion_isLimit (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) := by
  obtain ⟨d, hd, hdi⟩ := indFinitePoset_exists_limitCone κ hκ hex D
  have e := VertexIso.map (limitConeIso d c hd hc)
    (sliceOverPostcomp D (indInclusionPresheaf κ C))
  exact hdi.of_vertexIso e

/-- 元の有限半順序全錐の極限性は、元の前層への包含によって保存・反映される。 -/
lemma indFinitePoset_isLimit_iff_inclusion (c : JoinCone D) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) :=
  ⟨indFinitePoset_inclusion_isLimit κ hκ hex D c, ind_isLimit_of_inclusion κ D c⟩

end SerrePositivity.InfinityCategories.F2.Ind
