module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitLoopEvaluation
/-! # 実単位閉路の全正方形と元四面体の二射影面

概要：実閉路を導来 nerve の全正方形へ評価し、元四面体の二射影面へ厳密に因子分解する。
方針：写像空間の uncurry の自然性と幾何的単位面の再添字を接続する。
規約：実閉路・元入力・元四面体と全時間を変更しない。
使われ方：D の単位退化と F1B の相対比較を指定した実閉路へ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y
local notation "I" => (Δ[1] : SSet)

lemma dgGluingModelRightUnitLoop_evaluate :
    intervalMappingUncurry (dgGluingModelRightUnitLoop R C D M X Y).h =
      (I ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        (I ◁ (β_ P I).hom) ≫ (I ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 0 := by
  rw [dgGluingModelRightUnitLoop_h R C D M X Y]
  simp only [intervalMappingUncurry_precomp, dgGluingNativeUnitCapIntervalTriangle_evaluate]

lemma dgGluingModelLeftUnitLoop_evaluate :
    intervalMappingUncurry (dgGluingModelLeftUnitLoop R C D M X Y).h =
      (I ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        (I ◁ (β_ P I).hom) ≫ (I ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
          dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 2 := by
  rw [dgGluingModelLeftUnitLoop_h R C D M X Y]
  simp only [intervalMappingUncurry_precomp, dgGluingNativeUnitCapIntervalTriangle_evaluate]

lemma dgGluingModelRightUnitLoop_tetrahedron_face :
    intervalMappingUncurry (dgGluingModelRightUnitLoop R C D M X Y).h =
      (I ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          prismEndpoint 1 (Δ[3] ⊗ P) ≫
            dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  rw [dgGluingModelRightUnitLoop_evaluate R C D M X Y,
    dgGluingNativeUnitCapPastingTriangleFamily,
    reassoc_of% dgGluingUnitCapPastingDomain_first_unit P]

lemma dgGluingModelLeftUnitLoop_tetrahedron_face :
    intervalMappingUncurry (dgGluingModelLeftUnitLoop R C D M X Y).h =
      (I ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
          prismEndpoint 0 (Δ[3] ⊗ P) ≫
            dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  rw [dgGluingModelLeftUnitLoop_evaluate R C D M X Y,
    dgGluingNativeUnitCapPastingTriangleFamily,
    reassoc_of% dgGluingUnitCapPastingDomain_last_unit P]
end SerrePositivity.InfinityCategories
