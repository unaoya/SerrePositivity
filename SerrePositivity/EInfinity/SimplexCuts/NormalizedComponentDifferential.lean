module

public import SerrePositivity.EInfinity.SimplexCuts.CutSumBoundary
public import SerrePositivity.EInfinity.SimplexCuts.NormalizedBilinearExt

/-!
# 正規化した双線形切断成分の微分

Berger–Fresse §2.2.7、M14 L10の証明分割。
同じ基底と正規化生成元による外延性で、L09を双線形族の等式へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ正規化切断成分の係数側へ、元の線形削除微分を前置した像。 -/
def normalizedCoefficientBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    Surjection.degreeModule A (r + 1) d →ₗ[A] (AlexanderWhitney.chains A S).X q →ₗ[A]
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _ => 0
  | d + 1, q => by
    have h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
    exact ((normalizedComponent A S r d q).comp (Surjection.differential A (r + 1) d)).compr₂
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom

/-- 同じ正規化切断成分の入力側へ、元の正規化鎖微分を前置した像。 -/
def normalizedSimplexBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    Surjection.degreeModule A (r + 1) d →ₗ[A] (AlexanderWhitney.chains A S).X q →ₗ[A]
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | _, 0 => 0
  | d, q + 1 => by
    have h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact ((normalizedComponent A S r d q).compl₂
      ((AlexanderWhitney.chains A S).d (q + 1) q).hom).compr₂
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom

/-- C307：係数側の同じ微分の像を、元の基底・正規化生成元で評価する。 -/
lemma normalizedCoefficientBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    normalizedCoefficientBoundary A S r d q (Surjection.basis A (r + 1) d (ULift.up w))
        (AlexanderWhitney.generator A S q x) = cutSumCoefficientBoundary A S r d q w x := by
  cases d with
  | zero => rfl
  | succ d =>
    simp only [normalizedCoefficientBoundary, LinearMap.compr₂_apply, LinearMap.comp_apply,
      normalizedComponent_gen, cutSumCoefficientBoundary]

/-- C308：入力側の同じ微分の像を、元の基底・正規化生成元で評価する。 -/
lemma normalizedSimplexBoundary_generator (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    normalizedSimplexBoundary A S r d q (Surjection.basis A (r + 1) d (ULift.up w))
        (AlexanderWhitney.generator A S q x) = cutSumSimplexBoundary A S w q x := by
  cases q with
  | zero => rfl
  | succ q => rfl

/-- C304：同じ正規化した双線形族は、零次数を含めて元の二つの微分と両立する。 -/
lemma normalizedComponent_d (S : SSet.{0}) (r d q : ℕ) :
    (normalizedComponent A S r d q).compr₂
        ((power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
          (-((d + q : ℕ) : ℤ) + 1)).hom =
      normalizedCoefficientBoundary A S r d q +
        (-1 : ℤ) ^ d • normalizedSimplexBoundary A S r d q := by
  apply normalized_bilinear_ext A S
  intro w x
  simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.smul_apply,
    normalizedComponent_gen, rawComponent_value, normalizedCoefficientBoundary_generator,
    normalizedSimplexBoundary_generator]
  exact cutSum_boundary A S w x

end SerrePositivity.EInfinity.SimplexCuts
