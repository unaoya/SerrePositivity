module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialMonoidal
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerDegreeBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorAdjunctionMate

/-!
# 微分を消す操作とテンソル冪の指定基底

## 概要
Berger–Moerdijk §1 の代数の移送で、入力のテンソル冪の次数付き基底を照合する。

## 方針
強モノイダル比較を斉次テンソル上で計算し、指定された語の基底を保つことを示す。

## 規約
次数ごとの基底添字を共通に使う。

## 使われ方
セル段の次数付き同型を通した演算と重みの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- The strong monoidal comparison identifies the two actual tensor powers. -/
def eraseDifferentialPowerIso (K : Complex A) (n : ℕ) :
    power ((eraseDifferential A).obj K) n ≅ (eraseDifferential A).obj (power K n) := by
  letI := laxPowerComparison_isIso (eraseDifferential A) K n
  exact asIso (laxPowerComparison (eraseDifferential A) K n)

/-- The power comparison sends each specified homogeneous word basis vector to itself. -/
lemma eraseDifferentialPower_hom_basis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (n : ℕ) (i : ℤ)
    (x : powerGradedIndex I n i) :
    (laxPowerComparison (eraseDifferential A) K n).f i
      (powerGradedBasis (K := (eraseDifferential A).obj K) b n i x) =
        powerGradedBasis (K := K) b n i x := by
  induction n generalizing i with
  | zero =>
    change (eraseDifferentialUnitIso A).hom.f i (unitDegreeBasis (A := A) i x) = _
    rw [eraseDifferentialUnitIso_hom_f]
    rfl
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    change (eraseDifferentialTensorIso A K (power K n)).hom.f i
      ((cochainTensorMap (𝟙 ((eraseDifferential A).obj K))
        (laxPowerComparison (eraseDifferential A) K n)).f i
        (tensorGradedBasis (K := (eraseDifferential A).obj K)
          b (powerGradedBasis (K := (eraseDifferential A).obj K) b n) i ⟨a, z, y⟩)) =
      tensorGradedBasis (K := K) b (powerGradedBasis (K := K) b n) i ⟨a, z, y⟩
    rw [eraseDifferentialTensorIso_hom_f, tensorGradedBasis_apply, tensorGradedBasis_apply]
    change (cochainTensorMap (𝟙 ((eraseDifferential A).obj K))
      (laxPowerComparison (eraseDifferential A) K n)).f i
        (ιTensorObj ((eraseDifferential A).obj K) (power ((eraseDifferential A).obj K) n)
          a.1.1 a.1.2 i a.2
          (b a.1.1 z ⊗ₜ[A]
            powerGradedBasis (K := (eraseDifferential A).obj K) b n a.1.2 y)) = _
    rw [cochainTensorMap_apply_ι, ih]
    rfl

/-- The inverse comparison also preserves every specified homogeneous word basis vector. -/
lemma eraseDifferentialPower_inv_basis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (n : ℕ) (i : ℤ)
    (x : powerGradedIndex I n i) :
    (eraseDifferentialPowerIso K n).inv.f i (powerGradedBasis (K := K) b n i x) =
      powerGradedBasis (K := (eraseDifferential A).obj K) b n i x := by
  let e := (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).mapIso
    (eraseDifferentialPowerIso K n)
  apply e.toLinearEquiv.injective
  change ((eraseDifferentialPowerIso K n).inv ≫ (eraseDifferentialPowerIso K n).hom).f i
      (powerGradedBasis (K := K) b n i x) =
    (laxPowerComparison (eraseDifferential A) K n).f i
      (powerGradedBasis (K := (eraseDifferential A).obj K) b n i x)
  rw [Iso.inv_hom_id, HomologicalComplex.id_f, eraseDifferentialPower_hom_basis]
  rfl

end SerrePositivity.EInfinity
