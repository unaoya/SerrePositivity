module
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
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits D] (f : C ⟶ D)
    (hf : ∀ (x : C _⦋0⦌) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (s.square ≫ f))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (R ≫ f) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSquareGrid_nonempty R z.vertex z.isTerminal
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInput_isPullback_of_raw_suspension (d.extension.full ≫ f) (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_evaluate]
    have hs := d.suspension_at_isSuspension z.isZero hR i j
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) 0 0) := {
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
