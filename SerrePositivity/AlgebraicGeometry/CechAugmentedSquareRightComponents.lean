module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRightNaturality
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseLeftRightSurjective

/-!
概要：元のF8の中心側の項を、同じEと中心の座標で照合する。
方針：元の直積の包含と射影で微分・自然性を計算する。
規約：元の中心からの負符号と選択済み零加群を保持する。
使われ方：元の中心側の核のtotalと増大二重Čechの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)

private instance (b : ℕ) : Subsingleton (s.rightSquare.C.X b) := by
  change Subsingleton (0 : ModuleCat.{u} R)
  exact ModuleCat.subsingleton_of_isZero (isZero_zero _)

private instance (b : ℕ) : Subsingleton (s.rightSquare.source.X (b + 1)) := by
  change Subsingleton (0 : ModuleCat.{u} R)
  exact ModuleCat.subsingleton_of_isZero (isZero_zero _)

/-- 同じ中心側のEの座標への包含。 -/
def rightEι (b : ℕ) : s.E.X b ⟶ s.rightSquare.totalComplex.X (b + 2) :=
  ModuleCat.ofHom (LinearMap.id.prod 0)

/-- 同じ中心側のEの座標からの射影。 -/
def rightEπ (b : ℕ) : s.rightSquare.totalComplex.X (b + 2) ⟶ s.E.X b :=
  ModuleCat.ofHom (LinearMap.fst R _ _)

/-- 同じ縦一次の中心の座標への包含。 -/
def rightCenterι : s.centerBase ⟶ s.rightSquare.totalComplex.X 1 :=
  ModuleCat.ofHom ((0 : _ →ₗ[R] _).prod LinearMap.id)

/-- 同じ縦一次の中心の座標からの射影。 -/
def rightCenterπ : s.rightSquare.totalComplex.X 1 ⟶ s.centerBase :=
  ModuleCat.ofHom (LinearMap.snd R _ _)

/-- Eの座標の包含・射影の合成は恒等射。 -/
theorem rightEι_π (b : ℕ) : s.rightEι b ≫ s.rightEπ b = 𝟙 _ := by ext x; rfl

/-- 元の中心側の各正次数でも射影・包含の合成は恒等射。 -/
theorem rightEπ_ι (b : ℕ) : s.rightEπ b ≫ s.rightEι b = 𝟙 _ := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  change (x.1, 0) = x
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- 中心の座標の包含・射影の合成は恒等射。 -/
theorem rightCenterι_π : s.rightCenterι ≫ s.rightCenterπ = 𝟙 _ := by ext x; rfl

/-- 元の縦一次の項でも射影・包含の合成は恒等射。 -/
theorem rightCenterπ_ι : s.rightCenterπ ≫ s.rightCenterι = 𝟙 _ := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  change (0, x.2) = x
  exact Prod.ext (Subsingleton.elim _ _) rfl

/-- Eの座標の縦微分は元のEの微分を保つ。 -/
theorem rightEι_d (b : ℕ) :
    s.rightEι b ≫ s.rightSquare.totalComplex.d (b + 2) (b + 3) =
      s.E.d b (b + 1) ≫ s.rightEι (b + 1) := by
  rw [show s.rightSquare.totalComplex.d (b + 2) (b + 3) =
    ModuleCat.ofHom (augmentedCechConeDifferential s.rightSquare.source s.rightSquare.E
      s.rightSquare.difference s.rightSquare.base s.rightSquare.augmentation (b + 2)) from by
      dsimp only [CechAugmentedSquare.totalComplex, augmentedCechCone]
      exact CochainComplex.of_d _ _ _]
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  apply Prod.ext
  · change (s.E.d b (b + 1)).hom x + 0 = (s.E.d b (b + 1)).hom x
    exact add_zero _
  · exact Subsingleton.elim _ _

/-- 元の中心からEへの辺は同じ負符号を持つ。 -/
theorem rightCenterι_d :
    s.rightCenterι ≫ s.rightSquare.totalComplex.d 1 2 =
      -(ModuleCat.ofHom s.center ≫ s.rightEι 0) := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  apply Prod.ext
  · change 0 - s.center x = -s.center x
    exact zero_sub _
  · exact Subsingleton.elim _ _

variable {s} {t : CechAugmentedSquare.{u} R} (m : Map s t)

/-- 元の四角形の射は同じEの座標の包含に自然。 -/
theorem rightEι_naturality (b : ℕ) :
    s.rightEι b ≫ m.onRightSquare.totalComplexMap.f (b + 2) =
      m.right.f b ≫ t.rightEι b := by ext x; rfl

/-- 元の四角形の射は同じ中心の座標の包含に自然。 -/
theorem rightCenterι_naturality :
    s.rightCenterι ≫ m.onRightSquare.totalComplexMap.f 1 =
      ModuleCat.ofHom m.center ≫ t.rightCenterι := by ext x; rfl

/-- 同じEの座標は元の基底射影で零になる。 -/
theorem rightEι_baseProjection (b : ℕ) :
    s.rightEι b ≫ ((Map.baseProjection s).onRightSquare.totalComplexMap).f (b + 2) = 0 := by
  ext x
  rfl

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
