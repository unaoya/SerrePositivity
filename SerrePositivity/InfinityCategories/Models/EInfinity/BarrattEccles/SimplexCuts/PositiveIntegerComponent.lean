module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedComponentDifferential

/-!
模型。文献の定義との比較は後で
# 同じ正規化切断成分の整数次数への延長

Berger–Fresse §2.2.6–7、M14 L10 の証明分割。
元の負自然数次数の成分を等しい次数の比較で移し、正次数を零にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の正 arity の成分を、両入力の同じ非正整数次数で読む（BF §2.2.6）。 -/
def positiveIntegerBilinear (S : SSet.{0}) (r : ℕ) (i j t : ℤ) (h : i + j = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X i →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X t :=
  if hi : i ≤ 0 then
    if hj : j ≤ 0 then
      ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r (-i).toNat (-j).toNat).comp
        (eqToHom (congrArg (fun z : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X z)
          (by omega : i = -(((-i).toNat : ℕ) : ℤ)))).hom).compl₂
        (eqToHom (congrArg (fun z : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X z)
          (by omega : j = -(((-j).toNat : ℕ) : ℤ)))).hom).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z)
          (by omega : -((((-i).toNat + (-j).toNat : ℕ) : ℤ)) = t))).hom)
    else 0
  else 0

/-- C305：負自然数次数では、指定した元の正規化成分そのもの。 -/
lemma positiveIntegerBilinear_neg (S : SSet.{0}) (r d q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) (-((d + q : ℕ) : ℤ)) (by omega) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r d q := by
  cases d <;> cases q <;> rfl

/-- C309：正の係数次数では、同じ零延長の零成分。 -/
lemma positiveIntegerBilinear_eq_zero_left (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hi : 0 < i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r i j t h = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear, show ¬i ≤ 0 by omega, dite_false]

/-- C310：正の入力次数では、同じ零延長の零成分。 -/
lemma positiveIntegerBilinear_eq_zero_right (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) (hj : 0 < j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r i j t h = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear
  split
  · simp only [show ¬j ≤ 0 by omega, dite_false]
  · rfl

/-- C311：同じ負次数の成分は、指定した和の次数へ等式移送したもの。 -/
lemma positiveIntegerBilinear_neg_target (S : SSet.{0}) (r d q : ℕ) (t : ℤ)
    (h : -(d : ℤ) + -(q : ℤ) = t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ)) t h =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r d q).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z)
          (by omega : -((d + q : ℕ) : ℤ) = t))).hom := by
  have ht : t = -((d + q : ℕ) : ℤ) := by omega
  subst ht
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
    (-((d + q : ℕ) : ℤ)) (by omega) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r d q
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg A S r d q

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
