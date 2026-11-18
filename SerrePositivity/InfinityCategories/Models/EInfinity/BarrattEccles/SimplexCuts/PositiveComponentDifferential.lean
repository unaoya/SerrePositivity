module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveIntegerComponent
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainDegrees

/-!
模型。文献の定義との比較は後で
# 同じ切断成分の二つの微分の次数比較

Berger–Fresse §2.2.7、M14 L10 の証明分割。
正規化した微分公式を、元の整数複体の係数・入力の微分へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- C312：同じ次数比較を前置した正規化成分の微分公式。 -/
lemma positiveComponent_d (S : SSet.{0}) (r d q : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(q : ℤ))) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ)) (-((d + q : ℕ) : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent A S r d q a b) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary A S r d q
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom a) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom b) +
    (-1 : ℤ)^d • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary A S r d q
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom a) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom b) := by
  exact congrArg (fun f => f ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom a)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom b)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent_d A S r d q)

/-- C313：係数側の正規化した微分像は、元の整数複体の同じ微分像。 -/
lemma positiveCoefficientBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X (-((d + 1 : ℕ) : ℤ)))
    (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(q : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary A S r (d + 1) q
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) (d + 1)).hom a) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).hom b) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-(((d + 1) + q : ℕ) : ℤ) + 1) (by omega)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) a) b := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg_target]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary, LinearMap.compr₂_apply,
    LinearMap.comp_apply, LinearMap.compl₂_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.surjection_d_neg_apply]

/-- C314：入力側の正規化した微分像は、元の整数複体の同じ微分像。 -/
lemma positiveSimplexBoundary_succ (S : SSet.{0}) (r d q : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X (-(d : ℤ)))
    (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-((q + 1 : ℕ) : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary A S r d (q + 1)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom a) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S (q + 1)).hom b) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (-(d : ℤ)) (-(q : ℤ))
      (-((d + (q + 1) : ℕ) : ℤ) + 1) (by omega) a
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg_target, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains_d_neg]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary, LinearMap.compr₂_apply,
    LinearMap.comp_apply, LinearMap.compl₂_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent]
  change _ = (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z)
    (by omega : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1))).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (r + 1) d).hom a)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).toLinearEquiv
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).toLinearEquiv.symm
          ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).d (q + 1) q
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S (q + 1)).hom b)))))
  rw [LinearEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
