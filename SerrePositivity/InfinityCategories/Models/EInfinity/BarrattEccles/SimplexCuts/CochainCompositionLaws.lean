module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainCompositionInput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryActionLaw

/-!
模型。文献の定義との比較は後で
# BF切断余作用の全arityの元の複体射の合成則

Berger–Fresse §1.2.4・§2.2.6、M14 L14/L16、報告 §388。
元の基底値の等式を二つの語基底と全正規化単体の外延性で延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

/-- L16：空語を含む全arityで元の実複体射の部分合成則（BF §2.2.6）。 -/
lemma coaction_comp_all (A : Type u) [CommRing A] (S : SSet.{0}) (m n : ℕ) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n k ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S (m + n) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction A S m n k := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficient_simplex_hom_ext A S (m + 1) n
  intro d e q u v x
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_input A S u v k x).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_basis_eq_iterated_all A S u v k x _ rfl)

/-- L14：空語を代入する場合も元の同じ実複体射の合成則（BF §2.2.6）。 -/
lemma coaction_comp_nullary (A : Type u) [CommRing A] (S : SSet.{0}) (m : ℕ) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m 0 k ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S m =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction A S m 0 k :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coaction_comp_all A S m 0 k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
