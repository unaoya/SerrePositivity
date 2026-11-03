module

public import SerrePositivity.InfinityCategories.F2.Idempotent.RelativeInitialRetracts
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.Core.PushoutShape

/-!
概要：全四角形の関手 ∞ 圏内の元の押し出し四角形の retract は押し出し。
方針：元の span の全余錐への制限で retract を写し、相対始点境界充填を戻す。
規約：単独の対象の retract でなく、元の全四角形の関手 ∞ 圏内の retract。
使われ方：完備化における双カルテジアンな四角形の全 coherent 分裂。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の押し出し四角形の全関手 ∞ 圏内の指定 retract は、同じ全四角形で押し出し。 -/
lemma isPushoutSquare_of_diagram_retract {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (r : VertexRetraction (functorVertex F) (functorVertex G)) (hG : IsPushoutSquare G) :
    IsPushoutSquare F := by
  let p := (pre spanCoconeSquareIso.hom).app X
  have rr : VertexRetraction (functorVertex (pushoutCocone F).val)
      (functorVertex (pushoutCocone G).val) := r.map (hoFunctor.map p).toFunctor
  have hg : InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X)
      (functorVertex (pushoutCocone G).val) := hG.initialBoundaryLifting
  exact (colimitCocones_vertex_iff (pushoutCocone F)).mp
    (initialBoundaryLifting_of_vertexRetraction _ rr hg)

end SerrePositivity.InfinityCategories.F2.Idempotent
