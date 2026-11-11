module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalLabelCoefficients
/-!
概要：普遍的な正規化係数を任意の単体へ移し、退化写像による押し出しが零となることを示す。
方針：Mathlib の P・PInfty の全自然性と元のラベル退化消滅を直接使う。
規約：普遍係数からの式を実 dg 加群の作用との比較前に切り離して証明する。
使われ方：ラベル正規化の退化消去を、同じ係数に線形な bar 作用へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan SSet
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R]

lemma dgCoherentBarLabelProjection_map {I J : SSet.{u}} (f : I ⟶ J) (n : ℕ)
    (z : I _⦋n⦌ →₀ R) :
    (ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌))
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection R I).f n z) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection R J).f n
        ((ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌)) z) := by
  exact (ConcreteCategory.congr_hom
    (PInfty_f_naturality n (CategoryTheory.Functor.whiskerRight f (ModuleCat.free R))) z).symm

lemma dgCoherentBarLabelStage_map {I J : SSet.{u}} (f : I ⟶ J) (n q : ℕ)
    (z : I _⦋n⦌ →₀ R) :
    (ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌))
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage R I q).f n z) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage R J q).f n
        ((ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌)) z) := by
  exact (ConcreteCategory.congr_hom
    (P_f_naturality q n (CategoryTheory.Functor.whiskerRight f (ModuleCat.free R))) z).symm

lemma dgCoherentBarUniversalCoefficients_degeneracy (n : ℕ) (j : Fin (n + 1)) :
    (ModuleCat.free R).map
      ((SSet.stdSimplex.map (SimplexCategory.σ j)).app (Opposite.op ⦋n + 1⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalCoefficients R (n + 1)) = 0 := by
  have h := dgCoherentBarLabelProjection_map R (SSet.stdSimplex.map (SimplexCategory.σ j))
    (n + 1) (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity (n + 1)))
  rw [ModuleCat.free_map_apply] at h
  have hs : ((SSet.stdSimplex.map (SimplexCategory.σ j)).app (Opposite.op ⦋n + 1⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity (n + 1)) =
      (Δ[n] : SSet.{u}).σ j (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n) := by
    apply SSet.stdSimplex.ext
    intro i
    rfl
  rw [hs] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection_degenerate R Δ[n]
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n) j)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
