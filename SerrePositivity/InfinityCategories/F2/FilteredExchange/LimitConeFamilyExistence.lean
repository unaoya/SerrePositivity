module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LimitConeFamilyReadback
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：各点の極限の存在から、元の図式を厳密に保つ coherent な極限錐の族を構成する。
方針：各点の錐を相対終点境界充填で全パラメータへ延長する。
規約：点での選択に自然性を仮定しない。使われ方：有限形状の貼り合わせの部分極限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 各点に極限があれば、元の形状への制限を厳密に保つ極限錐の coherent な族が存在。 -/
lemma exists_pointwiseLimitConeFamily {B K X : SSet.{u}} [Quasicategory X]
    (p : B ⟶ (ihom K).obj X)
    (hp : ∀ b : B _⦋0⦌,
      HasLimit ((functorVertexEquiv K X).symm (p.app (Opposite.op ⦋0⦌) b))) :
    ∃ q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X,
      q ≫ coneRestriction K X = p ∧
      ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b)) := by
  classical
  choose c hc using hp
  let v : B _⦋0⦌ → ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌ :=
    fun b => functorVertex (c b).val
  have hv (b : B _⦋0⦌) :
      (coneRestriction K X).app (Opposite.op ⦋0⦌) (v b) = p.app (Opposite.op ⦋0⦌) b := by
    change functorVertex (joinInr Δ[0] K ≫ (c b).val) = _
    rw [(c b).property]
    exact (functorVertexEquiv K X).apply_symm_apply _
  have ht (b : B _⦋0⦌) : TerminalBoundaryLifting (coneRestriction K X) (v b) :=
    terminalBoundaryLifting_coneRestriction_of_isLimitCone (c b) (hc b)
  obtain ⟨q, hq, hqv⟩ := exists_lift_of_terminal_vertex_lifts (coneRestriction K X) p v hv ht
  refine ⟨q, hq, ?_⟩
  intro b
  have he : functorVertexConeMap (q.app (Opposite.op ⦋0⦌) b) = (c b).val := by
    rw [hqv b]
    exact (functorVertexEquiv _ _).symm_apply_apply (c b).val
  exact (isLimitCone_functorVertexCone_iff_of_val (c b) _ he).mpr (hc b)

end SerrePositivity.InfinityCategories.F2
