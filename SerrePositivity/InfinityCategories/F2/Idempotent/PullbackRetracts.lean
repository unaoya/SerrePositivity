module

public import SerrePositivity.InfinityCategories.F2.Idempotent.PushoutRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.DiagramOppositeRetracts
public import SerrePositivity.InfinityCategories.F1.SquareOpposite

/-!
概要：全四角形の関手 ∞ 圏内の元の引き戻し四角形の retract は引き戻し。
方針：元の全図式と添字を反転し、反転四角形への制限で押し出しの閉性を使う。
規約：元の同じ全四角形の普遍性を結論する。
使われ方：完備化の双カルテジアンな零角四角形の coherent 分裂。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の引き戻し四角形の全関手 ∞ 圏内の指定 retract は、同じ全四角形で引き戻し。 -/
lemma isPullbackSquare_of_diagram_retract {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (r : VertexRetraction (functorVertex F) (functorVertex G)) (hG : IsPullbackSquare G) :
    IsPullbackSquare F := by
  let j : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ ((Δ[1] : SSet.{u}) ⊗ Δ[1]).op :=
    (((stdSimplex.opIso ⦋1⦌).inv ▷ Δ[1]) ≫
      ((Δ[1] : SSet.{u}).op ◁ (stdSimplex.opIso ⦋1⦌).inv)) ≫
        (opTensorIso Δ[1] Δ[1]).hom
  have ho := diagram_retract_op F G ⟨r⟩
  have hr := ho.map ((pre j).app X.op)
  change IsVertexRetractOf (functorVertex (reverseGrid F)) (functorVertex (reverseGrid G)) at hr
  exact (isPullbackSquare_iff_reverseGrid F).mpr
    (isPushoutSquare_of_diagram_retract (reverseGrid F) (reverseGrid G) hr.some
      ((isPullbackSquare_iff_reverseGrid G).mp hG))

end SerrePositivity.InfinityCategories.F2.Idempotent
