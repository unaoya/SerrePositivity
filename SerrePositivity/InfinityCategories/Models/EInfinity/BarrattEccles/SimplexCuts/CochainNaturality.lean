module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexPairGeneratorExt
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainActionGenerator
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainNullaryAction
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
# BF切断余作用の全arityの自然性

Berger–Fresse §2.2.6、M14 L15、報告 §390。
同じ全Cutの自然性と指定AW余単位の自然性を元の複体射へ延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全Cut和の自然性（BF §2.2.6）。 -/
lemma cutSum_map {S T : SSet.{0}} (f : S ⟶ T)
    {r d q : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (_root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) (r + 1)).f (-((d + q : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S u x) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A T u (f.app _ x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component_index_naturality A]
  · simp only [map_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm_map]
  · congr 1
    congr 1
    omega

/-- L15：全arityで同じBF複体射は単体集合の射に自然（BF §2.2.6）。 -/
lemma coaction_natural {S T : SSet.{0}} (f : S ⟶ T) (r : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r ◁ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A T r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S r ≫ _root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) r := by
  cases r with
  | zero =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_zero_eq_nullaryAction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_zero_eq_nullaryAction]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryAction, _root_.SerrePositivity.TensorPowers.map, Category.assoc]
    rw [whisker_exchange_assoc, leftUnitor_naturality_assoc,
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural]
    exact (Category.comp_id _).symm
  | succ r =>
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficient_simplex_pair_hom_ext A S (r + 1)
    intro d q u x
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_naturality,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_basis_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_basis_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_map]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
