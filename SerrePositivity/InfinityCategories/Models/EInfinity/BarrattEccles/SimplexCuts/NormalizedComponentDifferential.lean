module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutSumBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedBilinearExt

/-!
模型。文献の定義との比較は後で
# 正規化した双線形切断成分の微分

Berger–Fresse §2.2.7、M14 L10の証明分割。
同じ基底と正規化生成元による外延性で、L09を双線形族の等式へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ正規化切断成分の係数側へ、元の線形削除微分を前置した像。 -/
def normalizedCoefficientBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d →ₗ[A] (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _ => 0
  | d + 1, q => by
    have h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
    exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (r + 1) d)).compr₂
      (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom

/-- 同じ正規化切断成分の入力側へ、元の正規化鎖微分を前置した像。 -/
def normalizedSimplexBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (r + 1) d →ₗ[A] (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | _, 0 => 0
  | d, q + 1 => by
    have h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q).compl₂
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).d (q + 1) q).hom).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom

/-- C307：係数側の同じ微分の像を、元の基底・正規化生成元で評価する。 -/
lemma normalizedCoefficientBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up w))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumCoefficientBoundary A S r d q w x := by
  cases d with
  | zero => rfl
  | succ d =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary, LinearMap.compr₂_apply, LinearMap.comp_apply,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent_gen, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumCoefficientBoundary]

/-- C308：入力側の同じ微分の像を、元の基底・正規化生成元で評価する。 -/
lemma normalizedSimplexBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up w))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary A S w q x := by
  cases q with
  | zero => rfl
  | succ q => rfl

/-- C304：同じ正規化した双線形族は、零次数を含めて元の二つの微分と両立する。 -/
lemma normalizedComponent_d (S : SSet.{0}) (r d q : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q).compr₂
        ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
          (-((d + q : ℕ) : ℤ) + 1)).hom =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary A S r d q +
        (-1 : ℤ) ^ d • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary A S r d q := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalized_bilinear_ext A S
  intro w x
  simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.smul_apply,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent_gen, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_value, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary_generator,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary_generator]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_boundary A S w x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
