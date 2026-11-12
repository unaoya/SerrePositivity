module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryPositive
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryLast
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalCompositeBasis
/-!
概要：標準単体の恒等基底上で Dold–Kan 境界の普遍係数を計算する。
方針：一般の面和表示を自由加群で評価し、二写像の基底作用を合成ラベルへ戻す。
規約：元の Hσ を評価し、係数の一致を明示仮定にしない。
使われ方：実 bar の正規化境界と普遍係数作用の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan SSet
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R]

def dgCoherentBarUniversalBoundaryCoefficients (n q : ℕ) :
    ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R :=
  (Hσ q (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n])).f n
    (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n))

lemma dgCoherentBarUniversalBoundaryCoefficients_positive {n q a : ℕ} (hn : n = a + q) :
    dgCoherentBarUniversalBoundaryCoefficients R (n + 1) q =
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (a + 1) • ((-1 : ℤ) ^ (i.val + 1) •
      ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ i.succ ≫ SimplexCategory.σ ⟨a + 1, by omega⟩)))) +
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ a • ((-1 : ℤ) ^ (i.val + 1) •
      ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.σ ⟨a, by omega⟩ ≫ SimplexCategory.δ i.succ))) := by
  have h := LinearMap.congr_fun
    (congrArg (fun f => ModuleCat.Hom.hom f)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundary_positive (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n + 1]) hn))
    (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity (n + 1)))
  simp only [ModuleCat.hom_add, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    SimplicialObject.δ, SimplicialObject.σ, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule,
    CategoryTheory.Functor.comp_map, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalComposite_basis R] at h
  exact h

lemma dgCoherentBarUniversalBoundaryCoefficients_last (n : ℕ) :
    dgCoherentBarUniversalBoundaryCoefficients R (n + 1) (n + 1) =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 2) •
      ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ i.succ.succ ≫ SimplexCategory.σ (0 : Fin (n + 2)))) := by
  have h := LinearMap.congr_fun
    (congrArg (fun f => ModuleCat.Hom.hom f)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundary_last (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n + 1]) n))
    (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity (n + 1)))
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    SimplicialObject.δ, SimplicialObject.σ, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule,
    CategoryTheory.Functor.comp_map, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalComposite_basis R] at h
  exact h

lemma dgCoherentBarUniversalBoundaryCoefficients_above {n q : ℕ} (hq : n + 1 < q) :
    dgCoherentBarUniversalBoundaryCoefficients R (n + 1) q = 0 := by
  unfold dgCoherentBarUniversalBoundaryCoefficients
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundary_above _ hq]
  rfl

lemma dgCoherentBarUniversalBoundaryCoefficients_vertex (q : ℕ) :
    dgCoherentBarUniversalBoundaryCoefficients R 0 q = 0 := by
  unfold dgCoherentBarUniversalBoundaryCoefficients
  rw [Hσ_eq_zero q]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
