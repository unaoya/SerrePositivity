module

public import SerrePositivity.InfinityCategories.F2.Compact.ColimitClosureExchange
public import SerrePositivity.InfinityCategories.F2.Compact.Subcategory
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitExchangeInput
public import SerrePositivity.InfinityCategories.F2.Ind.FullCoconeLift
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Core.FiniteOppositeSSet

/-!
概要：明示した全有限交換の証拠から、compact 全部分圏の有限余極限を構成する。
方針：周囲の元の指定余極限頂点の compact 性を証明し、全余錐を厳密に持ち上げる。
規約：交換入力の存在は主張しない。小さい filtered 添字と標的の宇宙を分ける。
使われ方：F1b の全有限交換定理が提供された際の F2N-3(c) の接続口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 全有限交換の証拠を明示すると、元の有限余極限の頂点も compact。 -/
lemma isKappaCompact_finiteColimit_of_exchange {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})
    {K C : SSet.{max u v}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
    (a : JoinCocone D) (ha : IsColimitCone a)
    (hD : ∀ k : K _⦋0⦌, IsKappaCompact.{u, v} κ (D.app (Opposite.op ⦋0⦌) k)) :
    IsKappaCompact.{u, v} κ a.vertex :=
  isKappaCompact_colimit_of_exchange hκ a ha hD (hex.exchange K.op)

/-- 周囲に有限余極限があり全有限交換の証拠があれば、compact 全部分圏にも存在する。 -/
lemma hasFiniteColimits_kappaCompactObjects_of_exchange (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})
    (C : SSet.{max u v}) [Quasicategory C] [HasFiniteColimits C] :
    HasFiniteColimits (kappaCompactObjects.{u, v} κ C) := by
  constructor
  intro K hK D
  obtain ⟨c, hc⟩ := HasFiniteColimits.hasColimit (D ≫ kappaCompactInclusion κ C)
  have hx : IsKappaCompact.{u, v} κ c.vertex :=
    isKappaCompact_finiteColimit_of_exchange hκ hex c hc
      (fun k => fullSubcomplexOnVertices_vertex (D.app (Opposite.op ⦋0⦌) k))
  exact ⟨Ind.fullCoconeLift (IsKappaCompact.{u, v} κ) D c hx,
    Ind.fullCoconeLift_isColimit (IsKappaCompact.{u, v} κ) D c hx hc⟩

end SerrePositivity.InfinityCategories.F2.Compact
