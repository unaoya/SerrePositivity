module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleTimeConstantFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomTriangleVariableEdges
/-! # native 単位補正族の元 Hom 入力

概要：前側と終側の両補正族の可変辺を、元 Hom 上の同じ正本係数入力に同定する。
方針：実元入力の全時間一定性を輸送し、正本の元三角形端で評価して入力を回収する。
規約：端点だけでなく全時間の入力等式を保持する。
使われ方：四つの native 補正族を、元入力付き合成 fiber 内へ持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeOriginalRightIntervalDiagram :=
  (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
      (intervalMappingUncurry
      (dgGluingIdentityCommaSourceIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingNativeOriginalLeftIntervalDiagram :=
  (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
      (intervalMappingUncurry
      (dgGluingIdentityCommaReplacementIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_last_constant :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      (Δ[1] ◁ fst P (Δ[1] : SSet.{max (u + 1) v w})) ≫
      dgGluingNativeOriginalRightIntervalDiagram R C D M X Y := by
  have hV :=
    dgGluingPreNormalizeUnitCollarTriangleFamily_last_input.{u, max (u + 1) v} R RM IX IY (𝟙 _)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleTimeTransport_constant_edge.{max (u + 1) v, max (u + 1) v w} 0
    (dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (intervalMappingUncurry
      (dgGluingIdentityCommaSourceIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) hV
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simpa only [dgGluingNativePreNormalizeUnitCollarTriangleFamily,
    dgGluingNativeOriginalRightIntervalDiagram,
    dgGluingTriangleTimeTransport, Category.assoc] using h

lemma dgGluingNativePreUnitCapTriangleFamily_last_constant :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      (Δ[1] ◁ fst P (Δ[1] : SSet.{max (u + 1) v w})) ≫
      dgGluingNativeOriginalRightIntervalDiagram R C D M X Y := by
  have hV :=
    dgGluingPreUnitCapTriangleFamily_last.{u, max (u + 1) v} R RM IX IY (𝟙 _)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleTimeTransport_constant_edge.{max (u + 1) v, max (u + 1) v w} 0
    (dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (intervalMappingUncurry
      (dgGluingIdentityCommaSourceIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) hV
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simpa only [dgGluingNativePreUnitCapTriangleFamily,
    dgGluingNativeOriginalRightIntervalDiagram,
    dgGluingTriangleTimeTransport, Category.assoc] using h

lemma dgGluingNativeExitUnitCollarTriangleFamily_first_constant :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      (Δ[1] ◁ fst P (Δ[1] : SSet.{max (u + 1) v w})) ≫
      dgGluingNativeOriginalLeftIntervalDiagram R C D M X Y := by
  have hV :=
    dgGluingExitUnitCollarTriangleFamily_first_original.{u, max (u + 1) v} R RM IX IY (𝟙 _)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleTimeTransport_constant_edge.{max (u + 1) v, max (u + 1) v w} 2
    (dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (intervalMappingUncurry
      (dgGluingIdentityCommaReplacementIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) hV
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simpa only [dgGluingNativeExitUnitCollarTriangleFamily,
    dgGluingNativeOriginalLeftIntervalDiagram,
    dgGluingTriangleTimeTransport, Category.assoc] using h

lemma dgGluingNativeExitUnitCapTriangleFamily_first_constant :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      (Δ[1] ◁ fst P (Δ[1] : SSet.{max (u + 1) v w})) ≫
      dgGluingNativeOriginalLeftIntervalDiagram R C D M X Y := by
  have hV :=
    dgGluingExitUnitCapTriangleFamily_first.{u, max (u + 1) v} R RM IX IY (𝟙 _)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleTimeTransport_constant_edge.{max (u + 1) v, max (u + 1) v w} 2
    (dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (intervalMappingUncurry
      (dgGluingIdentityCommaReplacementIntervalFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))) hV
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simpa only [dgGluingNativeExitUnitCapTriangleFamily,
    dgGluingNativeOriginalLeftIntervalDiagram,
    dgGluingTriangleTimeTransport, Category.assoc] using h

lemma dgGluingNativeOriginalRightIntervalDiagram_eq :
    dgGluingNativeOriginalRightIntervalDiagram R C D M X Y =
    intervalMappingUncurry (dgGluingNativeHomModelMap R C D M X Y ≫
      dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  have h := dgGluingTriangleConstantFace_endpoint (0 : Fin 3) (1 : Fin 2)
    (dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y)
    (dgGluingNativeOriginalRightIntervalDiagram R C D M X Y)
    (dgGluingNativePreNormalizeUnitCollarTriangleFamily_last_constant R C D M X Y)
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at h
  erw [dgGluingNativePreNormalizeUnitCollarTriangleFamily_one R C D M X Y] at h
  have hn : (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) =
    (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
      (stdSimplex.δ (0 : Fin 3) ▷ _) := rfl
  erw [← Category.assoc, hn, Category.assoc,
    dgGluingLaxHomArrowTriangles_first_variable R C D M X Y] at h
  rw [intervalMappingUncurry_precomp]
  exact h

lemma dgGluingNativeOriginalLeftIntervalDiagram_eq :
    dgGluingNativeOriginalLeftIntervalDiagram R C D M X Y =
    intervalMappingUncurry (dgGluingNativeHomModelMap R C D M X Y ≫
      dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  have h := dgGluingTriangleConstantFace_endpoint (2 : Fin 3) (0 : Fin 2)
    (dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y)
    (dgGluingNativeOriginalLeftIntervalDiagram R C D M X Y)
    (dgGluingNativeExitUnitCollarTriangleFamily_first_constant R C D M X Y)
  simp only [ite_true] at h
  erw [dgGluingNativeExitUnitCollarTriangleFamily_zero R C D M X Y] at h
  have hn : (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) =
    (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
      (stdSimplex.δ (2 : Fin 3) ▷ _) := rfl
  erw [← Category.assoc, hn, Category.assoc,
    dgGluingLaxHomArrowTriangles_second_variable R C D M X Y] at h
  rw [intervalMappingUncurry_precomp]
  exact h


lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_last_input :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      intervalMappingUncurry (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
        dgGluingNativeHomModelMap R C D M X Y ≫
          dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  erw [dgGluingNativePreNormalizeUnitCollarTriangleFamily_last_constant R C D M X Y,
    dgGluingNativeOriginalRightIntervalDiagram_eq R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativePreUnitCapTriangleFamily_last_input :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      intervalMappingUncurry (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
        dgGluingNativeHomModelMap R C D M X Y ≫
          dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  erw [dgGluingNativePreUnitCapTriangleFamily_last_constant R C D M X Y,
    dgGluingNativeOriginalRightIntervalDiagram_eq R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativeExitUnitCollarTriangleFamily_first_input :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      intervalMappingUncurry (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
        dgGluingNativeHomModelMap R C D M X Y ≫
          dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  erw [dgGluingNativeExitUnitCollarTriangleFamily_first_constant R C D M X Y,
    dgGluingNativeOriginalLeftIntervalDiagram_eq R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativeExitUnitCapTriangleFamily_first_input :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      intervalMappingUncurry (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
        dgGluingNativeHomModelMap R C D M X Y ≫
          dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  erw [dgGluingNativeExitUnitCapTriangleFamily_first_constant R C D M X Y,
    dgGluingNativeOriginalLeftIntervalDiagram_eq R C D M X Y,
    ← intervalMappingUncurry_precomp]
end SerrePositivity.InfinityCategories
