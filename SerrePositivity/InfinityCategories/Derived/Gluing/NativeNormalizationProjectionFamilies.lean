module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexPrismEndpoints
/-! # 標準単体族の native 導来輸送と全 prism の二射影

概要：元加群の標準単体族を正本 Hom 入力上へ輸送し、全 augmentation prism の両射影を保持する。
方針：元 Hom 入力・単体の宇宙同型・同じ導来加群比較を順に適用する。
規約：元の族を変更せず、両端とも全単体上の射の等式を保つ。
使われ方：四面体の射影面の一致と単位退化を主経路へ移す。
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

def dgGluingNativeNormalizationSimplexProjection (n : ℕ)
    (V : (Δ[n] : SSet.{max (u + 1) v}) ⊗ DGNerve.pinchedHom R Q IX IY ⟶ dgNerve R E) :=
  (Δ[n] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} n V ≫
      dgGluingUniverseModuleDerivedComparison.{u,v,w} R C

lemma dgGluingNativeNormalizationSimplexPrism_endpoint (n : ℕ)
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[n] ⊗ DGNerve.pinchedHom R Q IX IY) ⟶ dgNerve R E) (i : Fin 2) :
    prismEndpoint i (Δ[n] ⊗ P) ≫ dgGluingNativeNormalizationSimplexPrism R C D M X Y n V =
      dgGluingNativeNormalizationSimplexProjection R C D M X Y n
        (prismEndpoint i (Δ[n] ⊗ DGNerve.pinchedHom R Q IX IY) ≫ V) := by
  rw [dgGluingNativeNormalizationSimplexPrism,
    dgGluingNativeNormalizationSimplexProjection, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc,
    reassoc_of% dgGluingUliftSimplexPrismFamily_endpoint n V i]

lemma dgGluingNativeNormalizationSimplexProjection_face {n : ℕ}
    (V : (Δ[n + 1] : SSet.{max (u + 1) v}) ⊗
      DGNerve.pinchedHom R Q IX IY ⟶ dgNerve R E) (i : Fin (n + 2)) :
    (stdSimplex.δ i ▷ P) ≫
      dgGluingNativeNormalizationSimplexProjection R C D M X Y (n + 1) V =
    dgGluingNativeNormalizationSimplexProjection R C D M X Y n
      ((stdSimplex.δ i ▷ DGNerve.pinchedHom R Q IX IY) ≫ V) := by
  calc
    _ = (Δ[n] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
        (stdSimplex.δ i ▷ _) ≫
          dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} (n + 1) V ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    _ = _ := by rw [reassoc_of% dgGluingUliftSimplexFamily_face V i]; rfl

lemma dgGluingNativeNormalizationSimplexProjection_degeneracy {n : ℕ}
    (V : (Δ[n] : SSet.{max (u + 1) v}) ⊗
      DGNerve.pinchedHom R Q IX IY ⟶ dgNerve R E) (i : Fin (n + 1)) :
    (stdSimplex.σ i ▷ P) ≫
      dgGluingNativeNormalizationSimplexProjection R C D M X Y n V =
    dgGluingNativeNormalizationSimplexProjection R C D M X Y (n + 1)
      ((stdSimplex.σ i ▷ DGNerve.pinchedHom R Q IX IY) ≫ V) := by
  calc
    _ = (Δ[n + 1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
        (stdSimplex.σ i ▷ _) ≫
          dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} n V ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    _ = _ := by
      rw [reassoc_of% dgGluingUliftSimplexFamily_restrict V
        (stdSimplex.σ i) (stdSimplex.σ i) (by rfl)]
      rfl
end SerrePositivity.InfinityCategories
