module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleSourceRestriction

/-!
概要：任意次元の pointed 全族を、指定点を被覆する始域へ制限する。
方針：底を被覆する条件を一点パラメータへ付け、同じ全単体の底の式へ代入する。
規約：元の全図式と全パラメータを保持。使われ方：実際の fiber 作用を表す切断族の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定点を被覆する任意の始域で制限した全族の底は、元の同じ単体の一点評価。 -/
lemma pointedSimplexSourceRestriction_projection {E B C : SSet.{u + 1}} {n : ℕ}
    (p : E ⟶ B) (b : B _⦋0⦌) (s : C ⟶ E) (hs : s ≫ p = SSet.const b)
    (H : (Δ[n] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (L : (Δ[n] : SSet.{u + 1}) ⊗ (E ⊗ (Δ[0] : SSet.{u + 1})) ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = (Δ[n] ◁ (p ▷ (Δ[0] : SSet.{u + 1}))) ≫ H) :
    (Δ[n] ◁ lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      L ≫ pointedSpaceProjection = fst Δ[n] C ≫ coherentTransformationPointDiagram H b := by
  rw [hL, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    sourceParameterPoint_projection p b s hs]
  rfl

end SerrePositivity.InfinityCategories.F2
