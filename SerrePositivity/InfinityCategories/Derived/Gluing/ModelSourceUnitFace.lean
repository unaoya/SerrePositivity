module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationProjectionFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceUnitFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitLoopTetrahedronFaces
/-!
概要：D の第一単位則を正本 Hom 模型上の同じ射影四面体へ輸送する。
方針：全単体族の宇宙輸送と Hom 模型同型の逆は退化と面に自然であることを用いる。
規約：元の全入力・四面体・Λ³₂ 上の固定面を保持する。
使われ方：左単位閉路の相対比較に残っていた厳密単位面を供給する。
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

lemma dgGluingNativeNormalizationRawTetrahedron_source_unit_face :
    (stdSimplex.δ (3 : Fin 4) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      prismEndpoint 0 (Δ[3] ⊗ DGNerve.pinchedHom R Q IX IY) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
    (stdSimplex.σ (0 : Fin 2) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      (stdSimplex.δ (2 : Fin 3) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ DGNerve.pinchedHom R Q IX IY) ≫
      prismEndpoint 0 (Δ[3] ⊗ DGNerve.pinchedHom R Q IX IY) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y :=
  dgGluingNormalizationSourceTetrahedron_unit_face.{u, max (u + 1) v} R E IX IY (𝟙 _)

lemma dgGluingNativeNormalizationAugmentationTetrahedron_source_unit_face :
    (stdSimplex.δ (3 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
      dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
    (stdSimplex.σ (0 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
      dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  simp only [dgGluingNativeNormalizationAugmentationTetrahedron,
    dgGluingNativeNormalizationSimplexPrism_endpoint,
    dgGluingNativeNormalizationSimplexProjection_face,
    dgGluingNativeNormalizationSimplexProjection_degeneracy]
  exact congrArg (dgGluingNativeNormalizationSimplexProjection R C D M X Y 2)
    (dgGluingNativeNormalizationRawTetrahedron_source_unit_face R C D M X Y)

lemma dgGluingModelUnitProjectionTetrahedron_source_unit_face :
    (stdSimplex.δ (3 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 =
    (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 := by
  calc
    _ = (Δ[2] ◁ (dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (3 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
          dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    _ = (Δ[2] ◁ (dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.σ (0 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
          (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ prismEndpoint 0 (Δ[3] ⊗ P) ≫
            dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      rw [dgGluingNativeNormalizationAugmentationTetrahedron_source_unit_face R C D M X Y]
    _ = _ := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
end SerrePositivity.InfinityCategories
