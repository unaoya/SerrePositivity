module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroEndPasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 指定した元の面を保ち、有限余極限で比較長方形を構成する。 -/
lemma exists_pushoutRectangle_of_left_bottom_of_finiteColimits {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = L ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F = τ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue L τ h
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction p k).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits.hasColimit (k ≫ p))
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting F _ hright
  rw [hleft]
  exact hL

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
