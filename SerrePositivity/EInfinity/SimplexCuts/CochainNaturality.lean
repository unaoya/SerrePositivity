module

public import SerrePositivity.EInfinity.SimplexCuts.SimplexPairGeneratorExt
public import SerrePositivity.EInfinity.SimplexCuts.CochainActionGenerator
public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryAction
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# BF切断余作用の全arityの自然性

Berger–Fresse §2.2.6、M14 L15、報告 §390。
同じ全Cutの自然性と指定AW余単位の自然性を元の複体射へ延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全Cut和の自然性（BF §2.2.6）。 -/
lemma cutSum_map {S T : SSet.{0}} (f : S ⟶ T)
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) (r + 1)).f (-((d + q : ℕ) : ℤ))
      (cutSum A S u x) = cutSum A T u (f.app _ x) := by
  unfold cutSum
  rw [component_index_naturality A]
  · simp only [map_sum, cutTerm_map]
  · congr 1
    congr 1
    omega

/-- L15：全arityで同じBF複体射は単体集合の射に自然（BF §2.2.6）。 -/
lemma coaction_natural {S T : SSet.{0}} (f : S ⟶ T) (r : ℕ) :
    (Surjection.complex A r ◁ (BarrattEccles.normalizedFunctor A).map f) ≫ cochainAction A T r =
      cochainAction A S r ≫ TensorPowers.map ((BarrattEccles.normalizedFunctor A).map f) r := by
  cases r with
  | zero =>
    rw [cochainAction_zero_eq_nullaryAction, cochainAction_zero_eq_nullaryAction]
    simp only [nullaryAction, TensorPowers.map, Category.assoc]
    rw [whisker_exchange_assoc, leftUnitor_naturality_assoc,
      AlexanderWhitney.cochainCounit_natural]
    exact (Category.comp_id _).symm
  | succ r =>
    apply coefficient_simplex_pair_hom_ext A S (r + 1)
    intro d q u x
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply, gen_naturality,
      cochainAction_basis_generator, cochainAction_basis_generator, cutSum_map]

end SerrePositivity.EInfinity.SimplexCuts
