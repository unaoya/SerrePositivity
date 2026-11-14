module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRepresentableLimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TwoZeroCornerBicartesianOfEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiniteOppositeColimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite

/-!
概要：有限極限と実 loop 関手の同値性から、任意の引き戻しの押し出し性を得る。
方針：反対圏の有限余極限で切除格子を作り、表現可能前層で判定する。
規約：元の圏の有限余極限や安定性を追加仮定にしない。
使われ方：HA 1.4.2.27 の安定性判定の一般零角への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：元の圏の反対圏では全ての懸垂四角形が引き戻しである。
方針：二つの零角を保つ双対化で既存の loop 判定へ戻す。
規約：元の有限余極限は仮定しない。使われ方：反対圏の切除の四面。 -/
lemma SuspensionSquare.op_isPullback_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {x : X.op _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square := by
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let F := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square ≫ q
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1) := t.zero_corner.unop
  have hw : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 0) := t.other_zero.unop
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F :=
    (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_postcomp_isIso _ q).mp
      ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare t.square).mp t.isPushout)
  have hp := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_iff_isPushout_of_zeroCorners_of_loopEquivalence
    s hs hΩ F hz hw).mp hF
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare t.square).mpr
    ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_postcomp_isIso _ q).mpr hp)

/-- 概要：実 loop 同値を持つ pointed な圏では全引き戻しが押し出しである。
方針：反対圏で任意の元の面を保つ格子を作り、その四つの懸垂面を使う。
規約：有限極限だけを入力し、一般安定性や有限余極限を仮定しない。
使われ方：一般の零角に対する fiber/cofiber 判定の順方向。 -/
theorem isPushoutSquare_of_isPullback_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.op
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSquareGrid_nonempty (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare R) z.vertex z.isTerminal
  have hdual := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare R).mp hR
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInput_isPullback_of_suspension_faces d.extension.full (by
    intro i j
    have ht := d.suspension_at_isSuspension z.isZero hdual i j
    let t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) 0 0) := {
      square := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full
      zero_corner := ht.1
      source_eq := rfl
      other_zero := ht.2.1
      isPushout := ht.2.2 }
    exact t.op_isPullback_of_loopEquivalence s hs hΩ)
  rw [d.square_restriction] at h
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare R).mpr h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.2.11" (partial := component) "仮定：点付き準圏に有限極限と loop 図式の切断を取り、その loop が同値（第3項では Lean が弱い：有限余極限は不要。第1・2項では Lean が強い：完全忠実性だけの条件に対して loop 同値を要求）。結論：安定性、および引き戻しなら押し出し（Lean が弱い：完全忠実な suspension または loop だけからの二方向をこの型は与えない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_of_isPullback_of_loopEquivalence
