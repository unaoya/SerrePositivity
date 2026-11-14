module

public import SerrePositivity.EInfinity.SimplexCuts.Normalization
public import SerrePositivity.EInfinity.Surjection.ZeroAugmentation
public import SerrePositivity.EInfinity.AlexanderWhitney.CochainCounit

/-!
# 空語の同じ augmentation による零 arity の余作用

Berger–Fresse §1.2.1・§2.2.6、M14 L10/L14 の零 arity の接続。
係数の空語を1へ送り、入力には元の AW 余単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の零次の空語 augmentation を同じ鎖複体の射にしたもの（BF §1.2.1）。 -/
def nullaryCoefficientChainAugmentation :
    Surjection.normalizedChains A 0 ⟶ tensorUnit (ModuleCat A) (.down ℕ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (Surjection.zeroAugmentation A 0), by
    have hz : Limits.IsZero ((Surjection.normalizedChains A 0).X 1) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (Surjection.degreeModule A 0 1)
      let _ : IsEmpty (Surjection.BasisWord 0 1) := ⟨fun w => Fin.elim0 (w.val 0)⟩
      change Subsingleton (ULift.{u} (Surjection.BasisWord 0 1) →₀ A)
      infer_instance
    exact hz.eq_of_src _ _⟩

/-- 同じ空語 augmentation の整数複体への零延長（BF §1.2.1）。 -/
def nullaryCoefficientAugmentation : Surjection.complex A 0 ⟶ 𝟙_ (Complex A) :=
  extendMap (nullaryCoefficientChainAugmentation A) ComplexShape.embeddingDownNat ≫
    (extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom

/-- 零 arity では、指定した空語 augmentation と元の AW 余単位を使う（BF §2.2.6）。 -/
def nullaryAction (S : SSet.{0}) :
    Surjection.complex A 0 ⊗ chains A S ⟶ power (chains A S) 0 :=
  (nullaryCoefficientAugmentation A ▷ chains A S) ≫
    (λ_ (chains A S)).hom ≫ AlexanderWhitney.cochainCounit A S

end SerrePositivity.EInfinity.SimplexCuts
