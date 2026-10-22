module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionFunctorComparison
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

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
namespace SerrePositivity.InfinityCategories

lemma suspensionFunctorOfFiniteColimits_pushout {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hR : IsPushoutSquare R) : IsPushoutSquare (R ≫ suspensionFunctorOfFiniteColimits X) := by
  obtain ⟨z, hz⟩ := HasZeroVertex.exists_zero (X := X)
  obtain ⟨d⟩ := excisionSquareGrid_nonempty R z hz.2
  have h := (isPushoutSquare_iff_transpose _).mp d.extension.final_pushout
  exact h.of_functorIso (d.suspension_functor_comparison hz hR)

end SerrePositivity.InfinityCategories
