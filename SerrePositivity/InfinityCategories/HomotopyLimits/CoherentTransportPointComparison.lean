module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportComparisonSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportTriangleVertex

/-!
概要：元の二単体による長辺比較円柱を、指定した始点の同じ点で評価する。
方針：元の円柱を点包含で前合成し、底・始点を全時刻で保持する。
規約：比較の選び直しをしない。使われ方：native な合成同型と共通根辺の比較の接続。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g) (v : (vertexFiber p a) _⦋0⦌)

/-- 元の輸送比較円柱を指定始点で評価した、実際の長辺比較。 -/
def coherentTransportPointComparisonHomotopy :
    SSet.Homotopy (prismVertexEvaluation (coherentTransportTriangleLongPrism p σ) v)
      (prismVertexEvaluation (transportEdgePrism p g) v) :=
  functorHomotopyPrecomp (coherentTransportComparison p σ).homotopy
    (lift (𝟙 Δ[1]) (SSet.const v))

/-- 同じ元の長辺の底を全時刻で固定する。 -/
lemma coherentTransportPointComparisonHomotopy_projection :
    (coherentTransportPointComparisonHomotopy p σ v).h ≫ p =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm g.edge := by
  change (((lift (𝟙 Δ[1]) (SSet.const v)) ▷ (Δ[1] : SSet.{u})) ≫
    (coherentTransportComparison p σ).homotopy.h) ≫ p = _
  rw [Category.assoc, (coherentTransportComparison p σ).projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc, ← Category.assoc
      (lift (𝟙 Δ[1]) (SSet.const v)), lift_fst, Category.id_comp]

/-- 始点は同じ元の fiber 頂点のまま、全時刻で固定する。 -/
lemma coherentTransportPointComparisonHomotopy_initial :
    (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u})) ≫
      (coherentTransportPointComparisonHomotopy p σ v).h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm v.val := by
  have hi : scaffoldFirstVertex 1 ≫ lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const v) =
      lift (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm v) ≫
        (scaffoldFirstVertex 1 ▷ vertexFiber p a) := by
    rw [scaffoldFirstVertex_whiskerRight]
    simp only [comp_lift, Category.comp_id, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
    rfl
  change (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u})) ≫
    (((lift (𝟙 Δ[1]) (SSet.const v)) ▷ (Δ[1] : SSet.{u})) ≫
      (coherentTransportComparison p σ).homotopy.h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hi,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    (coherentTransportComparison p σ).initial, ← Category.assoc, whiskerRight_fst]
  simp only [SSet.yonedaEquiv_symm_zero, SSet.comp_const, ← Category.assoc]
  rfl
/-- 点評価後も元の円柱の raw な射を前合成したものそのもの。 -/
lemma coherentTransportPointComparisonHomotopy_raw :
    (coherentTransportPointComparisonHomotopy p σ v).h =
      ((lift (𝟙 Δ[1]) (SSet.const v)) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportComparison p σ).homotopy.h := rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
