module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionFunctorComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：実格子の比較から同じ有限余極限 suspension 関手の押し出し保存を得る。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma suspensionFunctorOfFiniteColimits_pushout {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (R ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctorOfFiniteColimits X) := by
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := X)
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSquareGrid_nonempty R z hz.2
  have h := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp d.extension.final_pushout
  exact h.of_functorIso (d.suspension_functor_comparison hz hR)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
