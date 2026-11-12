module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalBoundarySupport
/-!
概要：Hσ の普遍係数の自然性と P の係数の一段再帰を与える。
方針：Mathlib の自然変換 natTransHσ と P_succ を自由加群の元で評価する。
規約：全ラベル上の等式であり、始点制限は支持を検証した後にだけ適用する。
使われ方：実正規化境界の係数比較を有限段の係数比較へ帰納する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan SSet
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R]

def dgCoherentBarLabelBoundaryLinear (n q : ℕ) :
    (((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R) →ₗ[R] (((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R) :=
  ((Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n])).f n).hom

lemma dgCoherentBarLabelBoundary_map {I J : SSet.{u}} (f : I ⟶ J) (n q : ℕ)
    (z : I _⦋n⦌ →₀ R) :
    (ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌))
      ((Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I)).f n z) =
    (Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R J)).f n
      ((ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌)) z) := by
  have h := congrArg
    (fun g : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R I ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R J => g.f n)
    ((natTransHσ (C := ModuleCat.{u} R) q).naturality
      (CategoryTheory.Functor.whiskerRight f (ModuleCat.free R)))
  change (ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌)) ≫
      (Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R J)).f n =
    (Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I)).f n ≫
      (ModuleCat.free R).map (f.app (Opposite.op ⦋n⦌)) at h
  exact (ConcreteCategory.congr_hom h z).symm

lemma dgCoherentBarUniversalBoundaryCoefficients_map {n : ℕ}
    (f : ⦋n⦌ ⟶ ⦋n⦌) (q : ℕ) :
    (ModuleCat.free R).map ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients R n q) =
    (Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n])).f n
      (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)) := by
  have h := dgCoherentBarLabelBoundary_map R (SSet.stdSimplex.map f) n q
    (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n))
  rw [ModuleCat.free_map_apply] at h
  have hf : ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n) = SSet.stdSimplex.objEquiv.symm f := by
    apply SSet.stdSimplex.ext
    intro i
    rfl
  rw [hf] at h
  exact h

lemma dgCoherentBarUniversalStageCoefficients_succ (n q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n (q + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n q +
        dgCoherentBarLabelBoundaryLinear R n q (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n q) := by
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
