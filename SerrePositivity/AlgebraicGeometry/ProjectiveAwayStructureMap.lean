module

public import SerrePositivity.AlgebraicGeometry.ReesScalarStructureMorphism
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra

/-!
概要：Proj の標準開の同型と、元の係数環上の構造射の整合性。
方針：次数零のスカラーの局所化を既存の係数写像と比較する。
規約：既存の projectiveHomogeneousAwayAlgebra と projectiveCechStructureMap を使う。
使われ方：Segre のアフィンチャートを同じ基底上で貼り合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] (f : A)
local instance projectiveAwayStructureAlgebra : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f

/-- 次数零から標準開へのスカラーの合成は、同じ基底環の係数写像。 -/
theorem projectiveAway_scalarMap :
    (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)).comp
      (projectiveScalarToZero G) = algebraMap R (HomogeneousLocalization.Away G f) := by
  apply RingHom.ext
  intro r
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  have hs : (algebraMap R (HomogeneousLocalization.Away G f) r).val =
      r • (1 : Localization.Away f) := by
    rw [Algebra.algebraMap_eq_smul_one, HomogeneousLocalization.val_smul,
      HomogeneousLocalization.val_one]
  rw [hs]
  change Localization.mk (algebraMap R A r) 1 = r • (1 : Localization.Away f)
  rw [Localization.mk_one_eq_algebraMap]
  simp only [Algebra.smul_def, mul_one]
  exact (IsScalarTower.algebraMap_apply R A (Localization.Away f) r).symm

/-- Proj のアフィン標準開は、同じ Spec R 上の標準開である。 -/
theorem projectiveAway_structureMap {d : ℕ} (hf : f ∈ G d) (hd : 0 < d) :
    Proj.awayι G f hf hd ≫ projectiveCechStructureMap G =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away G f))) := by
  rw [projectiveCechStructureMap_eq, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers f)).comp
      (projectiveScalarToZero G))) = _
  rw [projectiveAway_scalarMap]

end SerrePositivity.AlgebraicGeometry
