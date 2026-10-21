module
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport
public import SerrePositivity.KST.SConstruction.SerreCubeTensorIso
public import SerrePositivity.KST.SConstruction.MonoidalPowerCoherenceStep

/-! # 全対象を固定した元の三ブロック比較
概要：元の連結比較を左右の tensor 因子に作用させる射と、元の結合同型を与える。
方針：全ての tensor の四対象を固定し、元の射そのものを使う。
規約：新たな比較の選択を導入しない。使われ方：鎖比較の三因子の結合整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右側二ブロックの連結を分離する tensor 射。 -/
def serreCubeRightSplit (n m k : ℕ) :
    serreCubeComonoid A n ⊗ serreCubeComonoid A (m + k) ⟶
      serreCubeComonoid A n ⊗ (serreCubeComonoid A m ⊗ serreCubeComonoid A k) :=
  @tensorHom (Comon (Complex A)) _ _ (serreCubeComonoid A n) (serreCubeComonoid A n)
    (serreCubeComonoid A (m + k)) (serreCubeComonoid A m ⊗ serreCubeComonoid A k)
    (𝟙 (serreCubeComonoid A n)) (serreCubeTensorIso A m k).hom

/-- 元の左側二ブロックの連結を分離する tensor 射。 -/
def serreCubeLeftSplit (n m k : ℕ) :
    serreCubeComonoid A (n + m) ⊗ serreCubeComonoid A k ⟶
      (serreCubeComonoid A n ⊗ serreCubeComonoid A m) ⊗ serreCubeComonoid A k :=
  @tensorHom (Comon (Complex A)) _ _ (serreCubeComonoid A (n + m))
    (serreCubeComonoid A n ⊗ serreCubeComonoid A m)
    (serreCubeComonoid A k) (serreCubeComonoid A k)
    (serreCubeTensorIso A n m).hom (𝟙 (serreCubeComonoid A k))

/-- 元の三つの鎖立方体の結合同型の射。 -/
def serreCubeAssociatorHom (n m k : ℕ) :
    (serreCubeComonoid A n ⊗ serreCubeComonoid A m) ⊗ serreCubeComonoid A k ⟶
      serreCubeComonoid A n ⊗ (serreCubeComonoid A m ⊗ serreCubeComonoid A k) :=
  (α_ (serreCubeComonoid A n) (serreCubeComonoid A m) (serreCubeComonoid A k)).hom

/-- 元の次元移送と三因子の連結比較の可換性そのもの。 -/
def SerreCubeTensorAssociative (n m k : ℕ) : Prop :=
  MonoidalPowerCoherenceEquation
    (R := serreCubeComonoid A ((n + m) + k))
    (S := serreCubeComonoid A (n + (m + k)))
    (U := serreCubeComonoid A (n + m)) (V := serreCubeComonoid A (m + k))
    (X := serreCubeComonoid A n) (Y := serreCubeComonoid A m) (Z := serreCubeComonoid A k)
    (serreCubeDimensionMap A (Nat.add_assoc n m k))
    (serreCubeTensorIso A n (m + k)) (serreCubeTensorIso A m k)
    (serreCubeTensorIso A (n + m) k) (serreCubeTensorIso A n m)

end SerrePositivity.KST.SConstruction
