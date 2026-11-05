module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCollarIntervalTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapPastingTriangles
/-!
概要：元終域の実補正対角を同じ写像空間三角形の二面として保持する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
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
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetUnitCollarDiagonalTriangleFamily_two :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
          dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily R C D E p q X Y := by
  rw [dgGluingHomTargetUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    dgGluingUnitCollarDiagonalTriangleDomain_two]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_three R C D E p q X Y]
  rw [dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_reindex R C D E p q X Y]

lemma dgGluingHomTargetUnitCollarDiagonalTriangleFamily_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
          dgGluingHomTargetExitUnitCollarTriangleFamily R C D E p q X Y := by
  rw [dgGluingHomTargetUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    dgGluingUnitCollarDiagonalTriangleDomain_zero]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_zero R C D E p q X Y]
  rw [dgGluingHomTargetExitUnitCollarTriangleFamily_reindex R C D E p q X Y]
lemma dgGluingHomTargetUnitCollarDiagonalTriangleFamily_two_interval :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        intervalMappingUncurry (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
          dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCollarDiagonalTriangleFamily_two R C D E p q X Y,
    dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_diagonal R C D E p q X Y]

lemma dgGluingHomTargetUnitCollarDiagonalTriangleFamily_zero_interval :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        intervalMappingUncurry (dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
          dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCollarDiagonalTriangleFamily_zero R C D E p q X Y,
    dgGluingHomTargetExitUnitCollarTriangleFamily_diagonal R C D E p q X Y]
def dgGluingHomTargetUnitCollarIntervalTriangle :=
  dgGluingUnitCollarIntervalTriangle
    (dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y)
    (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetUnitCollarDiagonalTriangleFamily_two_interval R C D E p q X Y)
    (dgGluingHomTargetUnitCollarDiagonalTriangleFamily_zero_interval R C D E p q X Y)

lemma dgGluingHomTargetUnitCollarIntervalTriangle_evaluate :
    intervalMappingUncurry (dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y) =
      dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y :=
  dgGluingUnitCollarIntervalTriangle_evaluate _ _ _ _ _

lemma dgGluingHomTargetUnitCollarIntervalTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
          dgGluingHomTargetFirstInputDiagonal R C D E p q X Y :=
  dgGluingUnitCollarIntervalTriangle_two _ _ _ _ _

lemma dgGluingHomTargetUnitCollarIntervalTriangle_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
          dgGluingHomTargetLastInputDiagonal R C D E p q X Y :=
  dgGluingUnitCollarIntervalTriangle_zero _ _ _ _ _
end SerrePositivity.InfinityCategories
