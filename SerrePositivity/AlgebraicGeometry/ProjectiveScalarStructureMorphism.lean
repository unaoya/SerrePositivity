module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import SerrePositivity.AlgebraicGeometry.Blowup

/-!
概要：射影 Čech 側の大域スカラーが定める射と、実際の Proj・blowup の構造射の一致。
方針：分母1の大域スカラーと Proj.toSpecZero の同じ定義を、Γ–Spec の自然性で比較する。
規約：零次成分が大域切断全体であるとは仮定しない。
使われ方：G3 の実際のブローアップ四角形と 2f の構造射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G]

/-- 射影 Čech 側のスカラーの射は実際の Proj の構造射。 -/
theorem schemeScalarMorphism_projectiveScalar :
    schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) =
      Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (projectiveScalarToZero G)) := by
  unfold schemeScalarMorphism projectiveScalarToGlobalSections Proj.toSpecZero Proj.basicOpenToSpec
  simp only [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  have htop : (Proj G).toSpecΓ = (Scheme.topIso (Proj G)).inv ≫
      (⊤ : (Proj G).Opens).toSpecΓ := by
    rw [Scheme.Opens.toSpecΓ_top, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  rw [htop]
  simp only [Category.assoc, Scheme.isoOfEq_inv]
  have hEq : (eqToHom (Proj.basicOpen_one G).symm :
      (⊤ : (Proj G).Opens) ⟶ Proj.basicOpen G 1) = homOfLE (Proj.basicOpen_one G).ge :=
    Subsingleton.elim _ _
  rw [hEq, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]

/-- Rees 次数の零次スカラーは、既存の零次成分の同型の逆。 -/
theorem rees_projectiveScalarToZero (I : Ideal R) :
    projectiveScalarToZero (reesGrade I) = (reesZeroEquiv I).symm.toRingHom := by
  ext r
  rfl

end SerrePositivity.AlgebraicGeometry
