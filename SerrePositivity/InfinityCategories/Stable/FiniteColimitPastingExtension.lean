module
public import SerrePositivity.InfinityCategories.Stable.ZeroEndPasting
public import SerrePositivity.InfinityCategories.Stable.Definition

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
lemma exists_pushoutRectangle_of_left_bottom_of_finiteColimits {X : SSet.{u}}
    [Quasicategory X] [HasFiniteColimits X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingSquare F 2 = L ∧ pastingBottomTriangle F = τ ∧
        IsPushoutSquare (pastingSquare F 0) ∧ IsPushoutSquare (pastingSquare F 1) := by
  let G := pastingCornerGlue L τ h
  let p := pastingOuterBaseToCorner ≫ G
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have hp : HasColimit p := (hasColimit_iff_of_trivialRestriction p k).mpr
    (HasFiniteColimits.hasColimit (k ≫ p))
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply isPushoutSquare_pasting F _ hright
  rw [hleft]
  exact hL

end SerrePositivity.InfinityCategories
