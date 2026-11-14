module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarStructureMorphism

/-!
概要：Rees Proj の射影 Čech の構造射を実際の affine blowup の射へ戻す。
方針：一般の構造射の合成に名前を与え、その同じ証明を Rees に特殊化する。
規約：定義上同じ構造射を使い、具体的な構造層の環を再推論しない。
使われ方：G3 の 2f の四角形と実際のブローアップの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
section General
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G]

/-- 射影 Čech の大域スカラーが定める、定義上同じ構造射の合成。 -/
def projectiveCechStructureMap : Proj G ⟶ Spec (CommRingCat.of R) :=
  schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)

/-- 名前付けした同じ合成と Proj の実際の構造射の比較。 -/
theorem projectiveCechStructureMap_eq :
    projectiveCechStructureMap G =
      Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (projectiveScalarToZero G)) :=
  schemeScalarMorphism_projectiveScalar G
end General

/-- Rees Proj の射影 Čech 側の射は実際の affine blowup の射。 -/
theorem schemeScalarMorphism_rees {R : Type u} [CommRing R] (I : Ideal R) :
    projectiveCechStructureMap (reesGrade I) = affineBlowupπ I := by
  rw [projectiveCechStructureMap_eq, rees_projectiveScalarToZero]
  rfl

end SerrePositivity.AlgebraicGeometry
