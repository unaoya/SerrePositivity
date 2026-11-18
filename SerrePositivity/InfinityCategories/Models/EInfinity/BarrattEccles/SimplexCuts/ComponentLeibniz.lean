module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveIntegerLeibniz
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryAction
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
模型。文献の定義との比較は後で
# 切断成分の全 arity・全整数での Leibniz 則

Berger–Fresse §2.2.7、M14 L10。
正 arity の切断和と、零 arity の同じ空語 augmentation・AW 余単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の切断和の全整数成分。零 arity は指定した空語と AW の余単位。 -/
def component (S : SSet.{0}) : (r : ℕ) → (i j t : ℤ) → (h : i + j = t) →
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).X i →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X t
  | 0, i, j, t, h => TensorProduct.curry
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) i j t h ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryAction A S).f t).hom
  | r + 1, i, j, t, h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r i j t h

/-- L10：同じ切断成分は、全 arity・全整数で元の二つの微分と両立する。 -/
lemma component_d (S : SSet.{0}) (r : ℕ) (i j : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).X i) (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).d (i + j) (i + j + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component A S r i j (i + j) rfl a b) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component A S r (i + 1) j (i + j + 1) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).d i (i + 1) a) b +
      i.negOnePow • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component A S r i (j + 1) (i + j + 1) (by omega) a
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d j (j + 1) b) := by
  cases r with
  | zero =>
    exact ConcreteCategory.congr_hom (tensorComponent_d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryAction A S) i j) (a ⊗ₜ[A] b)
  | succ r => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_d A S r i j a b

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
