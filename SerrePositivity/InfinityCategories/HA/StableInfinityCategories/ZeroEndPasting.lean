module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroReturnPasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalCompositeTriangle
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-! # 零終点を付加する押し出し長方形

概要：下側の最後の頂点が零である合成二単体を、指定押し出しの右に付加する。
方針：外側 span の第一枝が零へ向かうことから余極限の存在を得て貼り合わせる。
規約：元の押し出しと下側二単体を保持。使われ方：任意の押し出しの引き戻し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：第一枝が終対象へ向かう指定 span は余極限を持つ。
方針：二枝を交換して既存の第二枝での判定を使う。
規約：安定性から余極限の存在を得る。使われ方：零終点を持つ外側 span。 -/
lemma hasColimit_span_of_terminal_first {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₁ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_restrict_of_precompositionEquivalence p _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso)).2
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_terminal_second
  rw [← Category.assoc, show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso.hom = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap from rfl, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_right]
  exact hz

/-- 概要：零終点を持つ底辺二単体を指定押し出しに付加し、両側押し出しの長方形を作る。
方針：外側 span の零へ向かう第一枝で余極限を作り、五頂点図式から延長する。
規約：左四角形と底辺二単体を厳密に保持。使われ方：安定性の任意の四角形への拡張。 -/
lemma exists_pushoutRectangle_of_zeroEnd {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = L ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F = τ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue L τ h
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction p k).2
    apply hasColimit_span_of_terminal_first
    have he : horn₂₀.ι₀₁ ≫ (k ≫ p) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
      change horn₂₀.ι₀₁ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _
      calc
        _ = (horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
        _ = _ := by
          rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterStandardSpan_bottomEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_bottom]
    rw [he]
    exact hz.2
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting F _ hright
  rw [hleft]
  exact hL

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
