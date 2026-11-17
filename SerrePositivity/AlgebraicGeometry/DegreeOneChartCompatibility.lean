module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneOverlap
public import SerrePositivity.AlgebraicGeometry.DegreeOneChartExt

/-!
概要：次数一の座標の遷移式から、Proj への二つの局所の射を比較する。
方針：交叉への局所化の延長を作り、生成元上で照合する。
規約：平坦性・非零な座標を仮定しない。
使われ方：Segre の行・列の局所の射を同じ法則で貼り合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A C : Type u} {ι : Type} [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable (a : ι → A) (ha : ∀ i, a i ∈ G 1)
variable (hs : Function.Surjective (MvPolynomial.aeval (R := R) a))
local instance degreeOneCompatibilityAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f
variable {f g : A} (hf : f ∈ G 1) (hg : g ∈ G 1)
variable (φ : HomogeneousLocalization.Away G f →ₐ[R] C)
variable (ψ : HomogeneousLocalization.Away G g →ₐ[R] C)
variable (hu : IsUnit (φ (homogeneousDegreeOneNormalize G hf g)))
variable (h : ∀ i, ψ (homogeneousDegreeOneNormalize G hg (a i)) *
    φ (homogeneousDegreeOneNormalize G hf g) = φ (homogeneousDegreeOneNormalize G hf (a i)))

include ha hs hu h

/-- 座標の遷移式を満たす二つの局所の写像は、同じ交叉への延長を持つ。 -/
theorem exists_degreeOneChart_overlapMap :
    ∃ L : HomogeneousLocalization.Away G (f * g) →ₐ[R] C,
      L.comp (homogeneousAwayMulRestrictionAlgHom G hg (rfl : f * g = f * g)) = φ ∧
      L.comp (homogeneousAwayMulRestrictionAlgHom G hf (mul_comm f g)) = ψ := by
  let := (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)).toAlgebra
  let : IsScalarTower R (HomogeneousLocalization.Away G f)
      (HomogeneousLocalization.Away G (f * g)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (homogeneousAwayMulRestrictionAlgHom G hg (rfl : f * g = f * g)).commutes r |>.symm
  let : IsLocalization.Away (homogeneousDegreeOneNormalize G hf g)
      (HomogeneousLocalization.Away G (f * g)) := by
    rw [homogeneousDegreeOneNormalize_eq_isLocalizationElem G hf hg]
    exact HomogeneousLocalization.Away.isLocalization_mul hf hg rfl (by decide)
  let L : HomogeneousLocalization.Away G (f * g) →ₐ[R] C :=
    IsLocalization.Away.liftAlgHom (homogeneousDegreeOneNormalize G hf g) hu
  have hL (z : HomogeneousLocalization.Away G f) :
      L (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g) z) = φ z := by
    exact IsLocalization.Away.lift_eq (homogeneousDegreeOneNormalize G hf g) hu z
  refine ⟨L, AlgHom.ext hL, ?_⟩
  apply degreeOneChart_algHom_ext G hg a hs
  intro k
  apply hu.mul_left_inj.mp
  change L (HomogeneousLocalization.awayMap G hf (mul_comm f g)
    (homogeneousDegreeOneNormalize G hg (a k))) * φ (homogeneousDegreeOneNormalize G hf g) = _
  calc
    _ = L (HomogeneousLocalization.awayMap G hf (mul_comm f g)
        (homogeneousDegreeOneNormalize G hg (a k)) *
        HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)
          (homogeneousDegreeOneNormalize G hf g)) := by rw [map_mul, hL]
    _ = L (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g)
        (homogeneousDegreeOneNormalize G hf (a k))) :=
      congrArg L (homogeneousDegreeOneRestriction_transition G hf hg (ha k))
    _ = φ (homogeneousDegreeOneNormalize G hf (a k)) := hL _
    _ = ψ (homogeneousDegreeOneNormalize G hg (a k)) *
        φ (homogeneousDegreeOneNormalize G hf g) := (h k).symm

/-- 同じ交叉上の遷移式は、二つの標準開から Proj への合成の一致を与える。 -/
theorem degreeOneChart_compat_of_transition :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Proj.awayι G f hf (by decide) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Proj.awayι G g hg (by decide) := by
  obtain ⟨L, hL, hR⟩ := exists_degreeOneChart_overlapMap G a ha hs hf hg φ ψ hu h
  have hleft : Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom L.toRingHom) ≫ Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap G hg (rfl : f * g = f * g))) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom φ.toRingHom) = Spec.map (CommRingCat.ofHom
      ((L.comp (homogeneousAwayMulRestrictionAlgHom G hg (rfl : f * g = f * g))).toRingHom))
    rw [hL]
  have hright : Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      Spec.map (CommRingCat.ofHom L.toRingHom) ≫ Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap G hf (mul_comm f g))) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.map (CommRingCat.ofHom
      ((L.comp (homogeneousAwayMulRestrictionAlgHom G hf (mul_comm f g))).toRingHom))
    rw [hR]
  rw [hleft, hright, Category.assoc, Category.assoc,
    Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

end SerrePositivity.AlgebraicGeometry
