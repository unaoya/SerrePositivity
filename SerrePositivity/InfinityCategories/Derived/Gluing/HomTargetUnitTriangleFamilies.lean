module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationTetrahedron
/-!
概要：元終域の四補正三角形を、同じ正規化四面体の指定面・指定対角として束ねる。
方針：全時間の有限再添字と実三角形評価を保持する。
規約：新しい面を選ばない。使われ方：六片の係数側貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ (P ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_reindex :
    dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily R C D E p q X Y =
    dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫
      dgGluingHomTargetPreAugmentationTriangle R C D E p q X Y := rfl

lemma dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  dgGluingHomTargetPreNormalizationInputPath_diagonal_evaluation R C D E p q X Y

def dgGluingHomTargetPreUnitCapTriangleFamily :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ (P ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetPreUnitCapTriangleFamily_reindex :
    dgGluingHomTargetPreUnitCapTriangleFamily R C D E p q X Y =
    dgGluingTriangleTimeReindex dgGluingFirstUnitCap ≫
      dgGluingHomTargetPreAugmentationTriangle R C D E p q X Y := rfl

lemma dgGluingHomTargetPreUnitCapTriangleFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingHomTargetPreUnitCapTriangleFamily R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  dgGluingHomTargetPreCapInputPath_diagonal_evaluation R C D E p q X Y

def dgGluingHomTargetExitUnitCollarTriangleFamily :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ (P ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetExitUnitCollarTriangleFamily_reindex :
    dgGluingHomTargetExitUnitCollarTriangleFamily R C D E p q X Y =
    dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
      dgGluingHomTargetExitAugmentationTriangle R C D E p q X Y := rfl

lemma dgGluingHomTargetExitUnitCollarTriangleFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingHomTargetExitUnitCollarTriangleFamily R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y) :=
  dgGluingHomTargetExitCollarInputPath_diagonal_evaluation R C D E p q X Y

def dgGluingHomTargetExitUnitCapTriangleFamily :
    (Δ[2] : SSet.{max (u + 1) v}) ⊗ (P ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetExitUnitCapTriangleFamily_reindex :
    dgGluingHomTargetExitUnitCapTriangleFamily R C D E p q X Y =
    dgGluingTriangleTimeReindex dgGluingLastUnitCap ≫
      dgGluingHomTargetExitAugmentationTriangle R C D E p q X Y := rfl

lemma dgGluingHomTargetExitUnitCapTriangleFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingHomTargetExitUnitCapTriangleFamily R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y) :=
  dgGluingHomTargetExitCapInputPath_diagonal_evaluation R C D E p q X Y

end SerrePositivity.InfinityCategories
