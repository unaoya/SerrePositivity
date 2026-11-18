module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficientAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCoefficient

/-!
# H⁰ の演算に用いる係数の部分合成

概要：BF §1・BM §1 の部分合成公理へ単位からの二係数を入力する。
方針：二係数の合成を明示し、係数自然性と単位子の整合性で二段作用へ移す。
規約：全 arity、零入力も含む。
使われ方：H⁰ の積の単位則と結合則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] TensorPowers.power

/-- 概要：単位からの係数射を E 代数の n 入力作用にする（BF §1）。
方針：単位因子を挿入して係数射を作用へ前合成する。
規約：係数は augmentation の条件なしに指定できる。
使われ方：単位・結合性に適した係数で H⁰ の演算を計算する。 -/
def coefficientOperation (X : (operad A).Algebra) (n : ℕ)
    (a : 𝟙_ (Complex A) ⟶ (operad A).arity n) : power X.carrier n ⟶ X.carrier :=
  (λ_ (power X.carrier n)).inv ≫ (a ▷ power X.carrier n) ≫ X.action n

/-- 概要：二つの単位からの係数射の部分合成（BF §1、BM §1）。
方針：単位を分け、二射をテンソルして E の部分合成を適用する。
規約：零 arity の内側係数を許す。
使われ方：H⁰ の二段作用の共通係数。 -/
def coefficientComposite (m n : ℕ) (i : Fin (m + 1))
    (a : 𝟙_ (Complex A) ⟶ (operad A).arity (m + 1))
    (b : 𝟙_ (Complex A) ⟶ (operad A).arity n) :
    𝟙_ (Complex A) ⟶ (operad A).arity (m + n) :=
  (λ_ (𝟙_ (Complex A))).inv ≫ (a ⊗ₘ b) ≫ (operad A).comp m n i

/-- 概要：合成係数による作用は内側作用の代入に一致（BF §1、BM §1）。
方針：代数の部分合成公理を二係数で前合成し、係数自然性と単位子を簡約する。
規約：零入力を含む全位置の複体射の等式。
使われ方：H⁰ の単位則・結合則を E の係数比較に帰着する。 -/
lemma coefficientOperation_comp (X : (operad A).Algebra) (m n : ℕ) (i : Fin (m + 1))
    (a : 𝟙_ (Complex A) ⟶ (operad A).arity (m + 1))
    (b : 𝟙_ (Complex A) ⟶ (operad A).arity n) :
    coefficientOperation X (m + n) (coefficientComposite m n i a b) =
      (λ_ (power X.carrier (m + n))).inv ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) m n i
          ((b ▷ power X.carrier n) ≫ X.action n) ≫ coefficientOperation X (m + 1) a := by
  simp only [coefficientOperation, coefficientComposite, comp_whiskerRight, Category.assoc]
  rw [X.comp_action, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionComposition_coeff,
    ← leftUnitor_tensor_inv_assoc, ← leftUnitor_inv_naturality_assoc]

end SerrePositivity.EInfinity.BarrattEccles
