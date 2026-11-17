module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRightNaturality
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseLeftRightSurjective

/-!
概要：元のF8のY側の各項を、同じCの座標で照合する。
方針：選択済み零加群を持つ元の直積の包含・射影で計算する。
規約：元の各項・微分の負符号・全てのMapを保持する。
使われ方：元の核のtotalと増大二重Čechの再索引。
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

private instance : Subsingleton s.leftSquare.centerBase := by
  change Subsingleton (0 : ModuleCat.{u} R)
  exact ModuleCat.subsingleton_of_isZero (isZero_zero _)

private instance (b : ℕ) : Subsingleton (s.leftSquare.E.X b) := by
  change Subsingleton (0 : ModuleCat.{u} R)
  exact ModuleCat.subsingleton_of_isZero (isZero_zero _)

/-- 同じY側の正の縦次数のCの座標への包含。 -/
def leftCι : ∀ b, s.C.X b ⟶ s.leftSquare.totalComplex.X (b + 1)
  | 0 => ModuleCat.ofHom (LinearMap.id.prod 0)
  | _ + 1 => ModuleCat.ofHom ((0 : _ →ₗ[R] _).prod LinearMap.id)

/-- 同じY側の正の縦次数からCの座標への射影。 -/
def leftCπ : ∀ b, s.leftSquare.totalComplex.X (b + 1) ⟶ s.C.X b
  | 0 => ModuleCat.ofHom (LinearMap.fst R _ _)
  | _ + 1 => ModuleCat.ofHom (LinearMap.snd R _ _)

/-- 元のCの座標での包含・射影の合成は恒等射。 -/
theorem leftCι_π (b : ℕ) : s.leftCι b ≫ s.leftCπ b = 𝟙 _ := by
  ext x
  cases b <;> rfl

/-- 同じY側の各項でも射影・包含の合成は恒等射。 -/
theorem leftCπ_ι (b : ℕ) : s.leftCπ b ≫ s.leftCι b = 𝟙 _ := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  cases b with
  | zero =>
    change (x.1, 0) = x
    exact Prod.ext rfl (Subsingleton.elim _ _)
  | succ b =>
    change (0, x.2) = x
    exact Prod.ext (Subsingleton.elim _ _) rfl

/-- 元のCの座標の縦微分は、元のCの微分の負符号。 -/
theorem leftCι_d (b : ℕ) :
    s.leftCι b ≫ s.leftSquare.totalComplex.d (b + 1) (b + 2) =
      -(s.C.d b (b + 1) ≫ s.leftCι (b + 1)) := by
  rw [show s.leftSquare.totalComplex.d (b + 1) (b + 2) =
    ModuleCat.ofHom (augmentedCechConeDifferential s.leftSquare.source s.leftSquare.E
      s.leftSquare.difference s.leftSquare.base s.leftSquare.augmentation (b + 1)) from by
      dsimp only [CechAugmentedSquare.totalComplex, augmentedCechCone]
      exact CochainComplex.of_d _ _ _]
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  ext x
  cases b with
  | zero =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  | succ b =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · change -((cechZeroTermExtension s.C (0 : ModuleCat.{u} R)).d
        (b + 1) (b + 2)).hom x = -(s.C.d (b + 1) (b + 2)).hom x
      rw [cechZeroTermExtension_d]
      rfl

/-- 元の基底からCへのスカラーは、同じY側の零次の微分になる。 -/
theorem scalar_leftCι :
    ModuleCat.ofHom s.scalar ≫ s.leftCι 0 = s.leftSquare.totalComplex.d 0 1 := by
  ext x
  rfl

variable {s} {t : CechAugmentedSquare.{u} R} (m : Map s t)

/-- 元の四角形の射は同じCの座標の包含に自然。 -/
theorem leftCι_naturality (b : ℕ) :
    s.leftCι b ≫ m.onLeftSquare.totalComplexMap.f (b + 1) =
      m.left.f b ≫ t.leftCι b := by
  ext x
  cases b <;> rfl

/-- 同じCの座標は、元の基底の射影で零になる。 -/
theorem leftCι_baseProjection (b : ℕ) :
    s.leftCι b ≫ ((Map.baseProjection s).onLeftSquare.totalComplexMap).f (b + 1) = 0 := by
  ext x
  cases b <;> rfl

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
