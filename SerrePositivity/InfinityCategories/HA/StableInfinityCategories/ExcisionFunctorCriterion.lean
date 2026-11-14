module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionCorners

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma sends_pushouts_to_pullbacks_of_suspensionSquares {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits D] (f : C ⟶ D)
    (hf : ∀ (x : C _⦋0⦌) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (s.square ≫ f))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (R ≫ f) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSquareGrid_nonempty R z.vertex z.isTerminal
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInput_isPullback_of_raw_suspension (d.extension.full ≫ f) (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_evaluate]
    have hs := d.suspension_at_isSuspension z.isZero hR i j
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) 0 0) := {
      square := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full
      zero_corner := hs.1
      source_eq := rfl
      other_zero := hs.2.1
      isPushout := hs.2.2 }
    have hfs := hf _ s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) ≫ f) at hfs
    simpa only [Category.assoc] using hfs)
  rw [← Category.assoc, d.square_restriction] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.2.1" (partial := component) "仮定：零頂点を持つ準圏間の保存条件と、有限（余）極限を持つ場合の押し出し判定（Lean が強い：縮約性の標的は零対象を持つ場合、切除性の判定は始域に有限余極限と標的に有限極限を要求）。結論：零頂点保存と押し出しを引き戻しに送る条件が読める（Lean が弱い：三つの充満部分 ∞ 圏の構成はこの宣言に含まれない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares
attribute [cite HA "1.4.2.13" (partial := direction) "仮定：点付きの始域と有限余極限・標的の有限極限を持ち、各 suspension 面の像が引き戻し（Lean が弱い：標的の零対象と縮約性は不要。HA の条件 (2) は縮約性の下で同じ引き戻し条件）。結論：全押し出しの像が引き戻し（Lean が弱い：この型は条件 (2) から (1) への向きで、η の同値による双条件は明示しない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares
attribute [cite HA "1.4.2.14" (partial := direction) "仮定：両準圏が安定で F が完全、または全 suspension 面の像の引き戻し性を与える（HA と一致する幾何学的条件）。結論：完全性から suspension 図式の保存が従い、引き戻し判定から全押し出しへ拡張する（Lean が弱い：標準比較 ΣF(X)→F(ΣX) の同値を明示した完全性との双条件はこの型に含まれない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares
attribute [cite HA "6.1.1.3" (partial := stronger-hyp) "仮定：n=1、C は零対象・有限余極限を持つ準圏、D は有限極限を持つ準圏、F は全 suspension square を pullback に送る（Lean が強い：C の pointed 性と suspension での保存を追加）。結論：F は全 pushout square を pullback square に送る（原典の一次の切除性の要求する結論にこの仮定で一致）。任意 n の cube による述語と Excn の全部分圏、一次の必要十分条件全体は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares
attribute [cite HA "6.1.1.5" (partial := stronger-hyp) "仮定：n=1、C は零対象・有限余極限を持つ準圏、D は有限極限を持つ準圏、F は全 suspension square を pullback に送る（Lean が強い：C の pointed 性と suspension での保存を追加）。結論：F は全 pushout square を pullback square に送る（原典の一次の切除性の要求する結論にこの仮定で一致）。任意 n の cube による述語と Excn の全部分圏、一次の必要十分条件全体は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sends_pushouts_to_pullbacks_of_suspensionSquares
