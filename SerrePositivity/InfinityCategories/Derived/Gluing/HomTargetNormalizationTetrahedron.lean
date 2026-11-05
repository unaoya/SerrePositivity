module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputDiagonalEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationCoherence
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceUnitFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationTargetUnitFace
/-!
概要：元終域の同じ正規化四面体と三標準面・両単位退化を構成する。
方針：元恒等 comma の全四面体へ augmentation を適用し、宇宙を元へ戻す。
規約：同じ元 Hom 入力・全四面体を保持する。使われ方：六片の係数側貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetAugmentationTetrahedron :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[3] ⊗ P) ⟶ dgNerve R E :=
  dgGluingNormalizationAugmentationTetrahedron R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingHomTargetPreAugmentationTriangle :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[2] ⊗ P) ⟶ dgNerve R E :=
  dgGluingPreNormalizeAugmentationTriangle.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingHomTargetPostAugmentationTriangle :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[2] ⊗ P) ⟶ dgNerve R E :=
  dgGluingPostNormalizeAugmentationTriangle.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingHomTargetExitAugmentationTriangle :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[2] ⊗ P) ⟶ dgNerve R E :=
  dgGluingExitAugmentationTriangle.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

lemma dgGluingHomTargetAugmentationTetrahedron_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ P)) ≫
      dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
    dgGluingHomTargetExitAugmentationTriangle R C D E p q X Y := by
  rw [dgGluingHomTargetAugmentationTetrahedron, ← Category.assoc,
    dgGluingNormalizationAugmentationTetrahedron_zero.{u, max (u + 1) v}
      R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)]
  rfl

lemma dgGluingHomTargetAugmentationTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ P)) ≫
      dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
    dgGluingHomTargetPostAugmentationTriangle R C D E p q X Y := by
  rw [dgGluingHomTargetAugmentationTetrahedron, ← Category.assoc,
    dgGluingNormalizationAugmentationTetrahedron_one.{u, max (u + 1) v}
      R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)]
  rfl

lemma dgGluingHomTargetAugmentationTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ P)) ≫
      dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
    dgGluingHomTargetPreAugmentationTriangle R C D E p q X Y := by
  rw [dgGluingHomTargetAugmentationTetrahedron, ← Category.assoc,
    dgGluingNormalizationAugmentationTetrahedron_three.{u, max (u + 1) v}
      R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)]
  rfl

def dgGluingHomTargetUnitProjectionTetrahedron (i : Fin 2) :=
  prismEndpoint i (Δ[3] ⊗ P) ≫ dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y

lemma dgGluingHomTargetUnitProjectionTetrahedron_source_unit_face :
    (stdSimplex.δ (3 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 =
    (stdSimplex.σ (0 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ P) ≫
        dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 :=
  dgGluingNormalizationSourceTetrahedron_unit_face.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetUnitProjectionTetrahedron_target_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 =
    (stdSimplex.σ (1 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
        dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 :=
  dgGluingNormalizationTargetTetrahedron_unit_face.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

end SerrePositivity.InfinityCategories
