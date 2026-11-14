module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceZeroTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberExists
/-!
概要：実 loop 図式切断と loop 同値から IsStable を結論する。
方針：有限極限による fiber、回転で得た cofiber、任意零角の同値を三条件へ渡す。
規約：有限余極限・ModelCategory・一般安定性を追加仮定にしない。
使われ方：nativeLoop を持つ実スペクトル圏への一般安定性判定。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した元の loop 同値から安定性を導く。
方針：零対象と全辺の fiber/cofiber、零角の双方向判定をまとめる。
規約：切断の終点等号と実 loop 関手の同値性を明示する。
使われ方：HA Corollary 1.4.2.27 の一般 loop 判定。 -/
theorem isStable_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p) f
  cofiber_exists f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquare_nonempty_of_loopEquivalence s hs hΩ f
  fiber_iff_cofiber t := t.isFiber_iff_isCofiber_of_loopEquivalence s hs hΩ

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.15" (partial := direction) "仮定：安定準圏、または点付き準圏と有限極限および指定ループ同値（逆向きは HA の懸垂・余ファイバー条件の双対）。結論：安定性から懸垂同値を得る。逆向きはループ版の安定性判定であり、懸垂版の入力から直接 IsStable を返す型は確認できない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence
attribute [cite HA "1.4.2.11" (partial := component) "仮定：点付き準圏に有限極限と loop 図式の切断を取り、その loop が同値（第3項では Lean が弱い：有限余極限は不要。第1・2項では Lean が強い：完全忠実性だけの条件に対して loop 同値を要求）。結論：安定性、および引き戻しなら押し出し（Lean が弱い：完全忠実な suspension または loop だけからの二方向をこの型は与えない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence
attribute [cite HA "1.4.2.27" (partial := component) "仮定：点付き準圏に有限極限と選択 loop を置く場合、または既に安定な場合（HA と一致する方向別の仮定）。結論：loop 同値から安定性、安定性から互いに逆な suspension と loop、loop 同値から対応する suspension 同値（Lean が弱い：有限余極限と suspension 同値だけを入力する安定性の逆方向はこれらの型に現れない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence
