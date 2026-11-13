module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeHopfCoproduct

/-!
# 自由比較の標準二色成分

HA 3.2.4.7。元の Schur 生成射を使い、二つの比較の共通の始域と指定係数射を固定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (R : Type u) [CommRing R] (X Y : Complex R) (m n : ℕ)

/-- 標準二色語から、元の自由代数の同じ Schur 生成射への包含。 -/
def freeStandardSource :
    (operad R).arity (m + n) ⊗ (power X m ⊗ power Y n) ⟶
      ((operad R).freeAlgebra (X ⊞ Y)).carrier :=
  ((operad R).arity (m + n) ◁
    ((binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n))) ≫
    schurι R (sequence R) (X ⊞ Y) (m + n)

/-- 指定 Hopf 二色係数射を、元の左右の Schur 生成射へ送る射。 -/
def freeStandardTarget :
    (operad R).arity (m + n) ⊗ (power X m ⊗ power Y n) ⟶
      ((operad R).freeAlgebra X).carrier ⊗ ((operad R).freeAlgebra Y).carrier :=
  (twoColorCoefficientComparison R m n ▷ (power X m ⊗ power Y n)) ≫
    tensorμ ((operad R).arity m) ((operad R).arity n) (power X m) (power Y n) ≫
      (schurι R (sequence R) X m ⊗ₘ schurι R (sequence R) Y n)

/-- 共通の標準語を前合成すると、厳密な比較は指定入力への実際の作用となる。 -/
lemma freeStandardSource_hopfComparison_arity
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    freeStandardSource R X Y m n ≫ (freeHopfComparison (hopf R) h0 X Y).hom =
      ((operad R).arity (m + n) ◁
        ((binaryTensorStandardPowersIso X Y m n).inv ≫
          binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) ≫
          TensorPowers.map (freeHopfComparisonInput (hopf R) h0 X Y) (m + n))) ≫
        (hopfTensorAlgebra (hopf R) ((operad R).freeAlgebra X)
          ((operad R).freeAlgebra Y)).action (m + n) := by
  have h := freeHopfComparison_arity (hopf R) h0 X Y (m + n)
  change schurι R (sequence R) (X ⊞ Y) (m + n) ≫
    (freeHopfComparison (hopf R) h0 X Y).hom = _ at h
  simp only [freeStandardSource, Category.assoc, whiskerLeft_comp]
  rw [h]

end SerrePositivity.EInfinity.BarrattEccles
