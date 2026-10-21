module
public import SerrePositivity.KST.SConstruction.SerreCubeTripleComparison
public import SerrePositivity.KST.SConstruction.MonoidalPowerCoherenceStep

/-! # 元の連結鎖比較の三因子結合整合性
概要：元の次元移送と同じ連結比較の三因子の可換性を、全有限次元で証明する。
方針：零段は右単位、更新は元の右端保持と抽象的な結合の帰納段階を使う。
規約：元の余モノイド射と同じ比較を保持する。使われ方：Serre 関手のモノイダル構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 第三ブロックが零次元のときの、元の結合比較の可換性。 -/
lemma serreCubeTensorAssociative_zero (n m : ℕ) : SerreCubeTensorAssociative A n m 0 := by
  have ht := monoidalPowerCoherence_unit (R := serreCubeComonoid A (n + m))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m) (serreCubeTensorIso A n m).hom
  dsimp only [SerreCubeTensorAssociative, MonoidalPowerCoherenceEquation,
    serreCubeRightSplit, serreCubeLeftSplit,
    serreCubeAssociatorHom]
  change 𝟙 (serreCubeComonoid A (n + m)) ≫ (serreCubeTensorIso A n m).hom ≫
      (𝟙 (serreCubeComonoid A n) ⊗ₘ (ρ_ (serreCubeComonoid A m)).inv) =
    (ρ_ (serreCubeComonoid A (n + m))).inv ≫
      ((serreCubeTensorIso A n m).hom ⊗ₘ 𝟙 (𝟙_ (Comon (Complex A)))) ≫
        (α_ (serreCubeComonoid A n) (serreCubeComonoid A m) (𝟙_ (Comon (Complex A)))).hom
  erw [Category.id_comp]
  exact ht

/-- 元の三ブロック比較を一つ更新した、同じ比較同型の可換式。 -/
def SerreCubeTensorAssociativeStep (n m k : ℕ) : Prop :=
  MonoidalPowerCoherenceStepEquation
    (R := serreCubeComonoid A ((n + m) + k))
    (S := serreCubeComonoid A (n + (m + k)))
    (U := serreCubeComonoid A (n + m)) (V := serreCubeComonoid A (m + k))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m)
    (Z := serreCubeComonoid A k) (I := serreIntervalComonoid A)
    (serreCubeDimensionMap A (Nat.add_assoc n m k))
    (serreCubeTensorIso A n (m + k)) (serreCubeTensorIso A m k)
    (serreCubeTensorIso A (n + m) k) (serreCubeTensorIso A n m)

/-- 元の三因子の可換性から、同じ右端更新の可換式を得る。 -/
lemma serreCubeTensorAssociative_step_of (n m k : ℕ)
    (h : SerreCubeTensorAssociative A n m k) : SerreCubeTensorAssociativeStep A n m k := by
  dsimp only [SerreCubeTensorAssociative, MonoidalPowerCoherenceEquation,
    serreCubeRightSplit, serreCubeLeftSplit,
    serreCubeAssociatorHom] at h
  exact monoidalPowerCoherence_step_equation
    (R := serreCubeComonoid A ((n + m) + k))
    (S := serreCubeComonoid A (n + (m + k)))
    (U := serreCubeComonoid A (n + m)) (V := serreCubeComonoid A (m + k))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m)
    (Z := serreCubeComonoid A k) (I := serreIntervalComonoid A)
    (serreCubeDimensionMap A (Nat.add_assoc n m k))
    (serreCubeTensorIso A n (m + k)) (serreCubeTensorIso A m k)
    (serreCubeTensorIso A (n + m) k) (serreCubeTensorIso A n m) h

/-- 元の更新式は、一段大きい元の連結比較そのものの可換性を回収する。 -/
lemma serreCubeTensorAssociative_succ_of_step (n m k : ℕ)
    (h : SerreCubeTensorAssociativeStep A n m k) :
    SerreCubeTensorAssociative A n m (k + 1) := by
  dsimp only [SerreCubeTensorAssociative]
  erw [serreCubeDimensionMap_assoc_succ A n m k,
    serreCubeTensorIso_succ A n (m + k), serreCubeTensorIso_succ A m k,
    serreCubeTensorIso_succ A (n + m) k]
  change SerreCubeTensorAssociativeStep A n m k
  exact h

/-- 第三ブロックの右端保持は、元の結合比較の可換性を保つ。 -/
lemma serreCubeTensorAssociative_succ (n m k : ℕ) (h : SerreCubeTensorAssociative A n m k) :
    SerreCubeTensorAssociative A n m (k + 1) :=
  serreCubeTensorAssociative_succ_of_step A n m k (serreCubeTensorAssociative_step_of A n m k h)

/-- 元の次元移送を保つ、全三因子の連結鎖比較の結合整合性。 -/
lemma serreCubeTensorAssociative_all (n m k : ℕ) : SerreCubeTensorAssociative A n m k := by
  induction k with
  | zero => exact serreCubeTensorAssociative_zero A n m
  | succ k ih => exact serreCubeTensorAssociative_succ A n m k ih

end SerrePositivity.KST.SConstruction
