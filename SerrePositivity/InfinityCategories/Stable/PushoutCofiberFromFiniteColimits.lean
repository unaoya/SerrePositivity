module
public import SerrePositivity.InfinityCategories.Stable.FiniteColimitPastingExtension
public import SerrePositivity.InfinityCategories.Stable.PushoutCofiberRectangle

/-!
概要：有限余極限から指定した押し出しの比較長方形を構成する。
方針：外側の有限 span の普遍余錐を貼り合わせ、元の面と底辺を厳密に保つ。
規約：安定性は仮定しない。使われ方：一般安定性判定の比較格子と回転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定した元の面を保ち、有限余極限で比較長方形を構成する。 -/
lemma nonempty_pushoutCofiberRectangle_of_finiteColimits {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteColimits X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L) :
    Nonempty (PushoutCofiberRectangle L) := by
  let z := chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ :=
    exists_terminalCompositeTriangle z.isTerminal (squareBottomArrow L)
  have h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    exists_pushoutRectangle_of_left_bottom_of_finiteColimits L hL τ h
  refine ⟨⟨F, hleft, ?_, hright, houter⟩⟩
  change IsZeroVertex ((pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
  rw [hbottom, hlast]
  exact z.isZero

end SerrePositivity.InfinityCategories
