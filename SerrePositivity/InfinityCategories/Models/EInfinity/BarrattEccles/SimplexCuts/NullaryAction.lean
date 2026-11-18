module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Normalization
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ZeroAugmentation
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit

/-!
模型。文献の定義との比較は後で
# 空語の同じ augmentation による零 arity の余作用

Berger–Fresse §1.2.1・§2.2.6、M14 L10/L14 の零 arity の接続。
係数の空語を1へ送り、入力には元の AW 余単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の零次の空語 augmentation を同じ鎖複体の射にしたもの（BF §1.2.1）。 -/
def nullaryCoefficientChainAugmentation :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A 0 ⟶ tensorUnit (ModuleCat A) (.down ℕ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A 0), by
    have hz : Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A 0).X 1) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A 0 1)
      let _ : IsEmpty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 1) := ⟨fun w => Fin.elim0 (w.val 0)⟩
      change Subsingleton (ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 1) →₀ A)
      infer_instance
    exact hz.eq_of_src _ _⟩

/-- 同じ空語 augmentation の整数複体への零延長（BF §1.2.1）。 -/
def nullaryCoefficientAugmentation : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0 ⟶ 𝟙_ (Complex A) :=
  extendMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientChainAugmentation A) ComplexShape.embeddingDownNat ≫
    (extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom

/-- 零 arity では、指定した空語 augmentation と元の AW 余単位を使う（BF §2.2.6）。 -/
def nullaryAction (S : SSet.{0}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S ⟶ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫
    (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)).hom ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
