module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationProjectionFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceTetrahedron
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitLoopTetrahedronFaces
/-! # 主経路の始側四面体の二つの終側面の厳密一致

概要：元 replacement 射影の二面の一致を、同じ導来 augmentation 四面体と主経路へ移す。
方針：全単体族の宇宙輸送と同じ Hom 模型同型の逆だけで入力を制限する。
規約：単位則や新たな比較仮定を使わず、選択済み四面体を保持する。
使われ方：左単位面の相対内角比較で二面を無条件に固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "E" => RightModule R C
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y

lemma dgGluingNativeNormalizationRawTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      prismEndpoint 0 (Δ[3] ⊗ DGNerve.pinchedHom R Q IX IY) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
    (stdSimplex.δ (0 : Fin 4) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      prismEndpoint 0 (Δ[3] ⊗ DGNerve.pinchedHom R Q IX IY) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y :=
  dgGluingNormalizationSourceTetrahedron_one_eq_zero.{u, max (u + 1) v} R E IX IY (𝟙 _)

lemma dgGluingNativeNormalizationAugmentationTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
      dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
    (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
      dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  simp only [dgGluingNativeNormalizationAugmentationTetrahedron,
    dgGluingNativeNormalizationSimplexPrism_endpoint,
    dgGluingNativeNormalizationSimplexProjection_face]
  exact congrArg (dgGluingNativeNormalizationSimplexProjection R C D M X Y 2)
    (dgGluingNativeNormalizationRawTetrahedron_source_faces R C D M X Y)

lemma dgGluingModelUnitProjectionTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 =
    (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 := by
  calc
    _ = (Δ[2] ◁ (dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (1 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
          dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    _ = (Δ[2] ◁ (dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
          dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      rw [dgGluingNativeNormalizationAugmentationTetrahedron_source_faces R C D M X Y]
    _ = _ := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
end SerrePositivity.InfinityCategories
