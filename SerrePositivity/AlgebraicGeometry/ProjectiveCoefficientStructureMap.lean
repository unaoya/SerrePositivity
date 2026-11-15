module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveAwayStructureMap

/-!
概要：係数移送の Proj の射と基底への構造射の可換性。
方針：全ての正次数の標準開でスカラーの像を比較する。
規約：次数一生成・平坦性・Noether 性を仮定しない。
使われ方：Proj の任意の係数移送の pullback の四角形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G]
local instance projectiveCoefficientStructureSourceAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f
local instance projectiveCoefficientStructureTargetAlgebra (f : A) :
    Algebra B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)) :=
  projectiveHomogeneousAwayAlgebra (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)

/-- 係数移送の任意の標準開の射は、基底環のスカラーを保存する。 -/
theorem projectiveCoefficientAwayMap_scalar (f : A) :
    (HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) f).comp
        (algebraMap R (HomogeneousLocalization.Away G f)) =
      (algebraMap B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B)
        ((1 : B) ⊗ₜ[R] f))).comp (algebraMap R B) := by
  rw [← projectiveAway_scalarMap G f,
    ← projectiveAway_scalarMap (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)]
  apply RingHom.ext
  intro r
  apply HomogeneousLocalization.val_injective
  change Localization.mk ((1 : B) ⊗ₜ[R] algebraMap R A r) 1 =
    Localization.mk (algebraMap B (B ⊗[R] A) (algebraMap R B r)) 1
  congr 1
  exact (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).commutes r

set_option backward.isDefEq.respectTransparency false in
/-- 係数移送の Proj の射は、元の係数環上の構造射と可換。 -/
theorem projectiveCoefficientMap_structureMap :
    projectiveCoefficientMap (B := B) G ≫ projectiveCechStructureMap G =
      projectiveCechStructureMap (fun n ↦ (G n).baseChange B) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  refine (Proj.mapAffineOpenCover (projectiveCoefficientGradedMap (B := B) G)
    (projectiveCoefficient_irrelevant_le_map G)).openCover.hom_ext _ _ fun s ↦ ?_
  change Proj.awayι _ (projectiveCoefficientGradedMap (B := B) G s.2.1) _ _ ≫
    (Proj.map (projectiveCoefficientGradedMap (B := B) G) _ ≫ _) =
    Proj.awayι _ (projectiveCoefficientGradedMap (B := B) G s.2.1) _ _ ≫
      (projectiveCechStructureMap (fun n ↦ (G n).baseChange B) ≫ _)
  rw [← Category.assoc,
    Proj.awayι_comp_map (projectiveCoefficientGradedMap (B := B) G)
      (projectiveCoefficient_irrelevant_le_map G) s.1.2 s.2.1 s.2.2]
  rw [Category.assoc, projectiveAway_structureMap G s.2.1 s.2.2 s.1.2,
    ← Category.assoc, projectiveAway_structureMap _ _ _ s.1.2,
    ← Spec.map_comp, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) s.2.1).comp
      (algebraMap R (HomogeneousLocalization.Away G s.2.1)))) = _
  rw [projectiveCoefficientAwayMap_scalar G s.2.1]
  rfl

end SerrePositivity.AlgebraicGeometry
