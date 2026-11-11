module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRelativeConePoint
public import SerrePositivity.KST.LocalizingInvariants.VerdierRelativeConeSuccessor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierRelativeConeShapeIso

/-!
概要：全次数の標準単体パラメータについて、元の有限境界付き商錐を回収する。
方針：一点での回収を基底に、左錐の相対貼合せと標準単体の形状同型で帰納する。
規約：零次を含め、全境界と全比較円柱を保持する。充満忠実性の結論は別途接続する。
使われ方：c5 の元の core 逆像射影の各 slice の有限錐を構成する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の有限境界を全時刻固定する商錐回収は、零次を含む全ての標準単体で成り立つ。 -/
lemma hasVerdierRelativeConeRecovery_simplex {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q.hom (Δ[n] : SSet.{u}) := by
  induction n with
  | zero => exact hasVerdierRelativeConeRecovery_point h
  | succ n ih =>
    let e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[n] ≅ (Δ[n + 1] : SSet.{u}) := by
      simpa only [Nat.zero_add] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.hasVerdierRelativeConeRecovery_of_iso q.hom e
      (hasVerdierRelativeConeRecovery_join h Δ[n] ih)

end SerrePositivity.KST.LocalizingInvariants
