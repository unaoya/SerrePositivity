module

public import SerrePositivity.AlgebraicGeometry.ProjectiveAwayStructureMap
public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneNormalization

/-!
概要：次数一の標準開の交叉への制限と、正規化した元の遷移の法則。
方針：既存の awayMap と IsLocalization_mul の元を同定する。
規約：分母が零因子でもよく、平坦性を仮定しない。
使われ方：Segre チャートの射を重なりで比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G]
local instance homogeneousOverlapAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f

/-- 同じ交叉への制限は、元の係数環上の代数写像である。 -/
def homogeneousAwayMulRestrictionAlgHom {f g x : A} {e : ℕ} (hg : g ∈ G e)
    (hx : x = f * g) : HomogeneousLocalization.Away G f →ₐ[R]
      HomogeneousLocalization.Away G x where
  __ := HomogeneousLocalization.awayMap G hg hx
  commutes' r := by
    rw [← projectiveAway_scalarMap G f, ← projectiveAway_scalarMap G x]
    exact HomogeneousLocalization.awayMap_fromZeroRingHom G hg hx (projectiveScalarToZero G r)

/-- 次数一では、交叉を切り出す元は同じ g/f の正規化。 -/
theorem homogeneousDegreeOneNormalize_eq_isLocalizationElem {f g : A}
    (hf : f ∈ G 1) (hg : g ∈ G 1) :
    homogeneousDegreeOneNormalize G hf g =
      HomogeneousLocalization.Away.isLocalizationElem hf hg := by
  rw [homogeneousDegreeOneNormalize_of_mem G hf g hg]
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]

/-- g/f は D(fg) への制限の後に単元となる。 -/
theorem isUnit_homogeneousDegreeOneNormalize_restrict {f g : A}
    (hf : f ∈ G 1) (hg : g ∈ G 1) :
    IsUnit (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)
      (homogeneousDegreeOneNormalize G hf g)) := by
  let := (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)).toAlgebra
  let : IsLocalization.Away (homogeneousDegreeOneNormalize G hf g)
      (HomogeneousLocalization.Away G (f * g)) := by
    rw [homogeneousDegreeOneNormalize_eq_isLocalizationElem G hf hg]
    exact HomogeneousLocalization.Away.isLocalization_mul hf hg rfl (by decide)
  exact IsLocalization.Away.algebraMap_isUnit (homogeneousDegreeOneNormalize G hf g)

/-- 次数一の座標の、二つの正規化の間の交叉上の遷移の式。 -/
theorem homogeneousDegreeOneRestriction_transition {f g x : A}
    (hf : f ∈ G 1) (hg : g ∈ G 1) (hx : x ∈ G 1) :
    HomogeneousLocalization.awayMap G hf (mul_comm f g)
        (homogeneousDegreeOneNormalize G hg x) *
      HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)
        (homogeneousDegreeOneNormalize G hf g) =
      HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)
        (homogeneousDegreeOneNormalize G hf x) := by
  rw [homogeneousDegreeOneNormalize_of_mem G hg x hx,
    homogeneousDegreeOneNormalize_of_mem G hf g hg,
    homogeneousDegreeOneNormalize_of_mem G hf x hx,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (f * g))
  rw [HomogeneousLocalization.val_mul]
  simp only [HomogeneousLocalization.Away.val_mk, pow_one, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

end SerrePositivity.AlgebraicGeometry
