module

public import SerrePositivity.KTheory.Adams.TensorPower.TensorCubeFiltration
public import Mathlib.CategoryTheory.CommSq
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent
public import SerrePositivity.PerfectComplex.Tensor.CyclicSum
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # テンソル三乗の低次の混合成分

## 概要

低次の混合成分への標準的な商写像と三つの成分の構造的な包含、次数ごとの持ち上げ、巡回作用との同変性、低次の層の再構成と完全性、低次の混合列の完全性と台を与える。

## 方針

成分は巡回作用で移り合う三つの因子の選び方で、次数ごとに分裂させて完全性を示す。

## 規約

「成分と完全性」と「回転と台」に分けてもよい（refactor-plan §6.4.1）。

## 使われ方

`TensorPower/TensorCubeClass`。
-/

@[expose] public noncomputable section

universe u

section TensorCubeLowMixedPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
private lemma comp_twice_equivariant_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A K M N : C} (i : A ⟶ K) (τA : A ⟶ A) (τK : K ⟶ K)
    (x : K ⟶ M) (z : M ⟶ N) (hc : i ≫ τK = τA ≫ i) (hz : i ≫ x = 0) :
    i ≫ τK ≫ τK ≫ x ≫ z = 0 := by
  calc
    _ = τA ≫ i ≫ τK ≫ x ≫ z := by
      simpa only [Category.assoc] using hc =≫ (τK ≫ x ≫ z)
    _ = τA ≫ τA ≫ i ≫ x ≫ z := by
      simpa only [Category.assoc] using τA ≫= (hc =≫ (x ≫ z))
    _ = 0 := by
      rw [← Category.assoc i x z, hz]
      simp only [zero_comp, comp_zero]

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract the first quotient factor, then lift the second factor into A. -/
def tensorCubeLowMixed0Partial : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₂ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₂
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeFirstLayerInclusion S.g ≫
    cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂)) (by
      change (tensorCubeFirstLayerInclusion S.g ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂)) ≫
        cochainTensorTripleMap (𝟙 S.X₃) S.g (𝟙 S.X₂) = 0
      simp only [Category.assoc, cochainTensorTripleMap, cochainTensorMap_comp,
        comp_id, id_comp]
      exact tensorCubeFirstLayerInclusion_pair0 S.g)

@[reassoc]
lemma tensorCubeLowMixed0Partial_inclusion :
    tensorCubeLowMixed0Partial S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) := by
  dsimp [tensorCubeLowMixed0Partial]
  exact Fork.IsLimit.lift_ι _

lemma tensorCubeLowMixed0Partial_quotient_zero :
    tensorCubeLowMixed0Partial S hS hproj ≫
      cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.g = 0 := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₃
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃))).mp
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.g ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) ≫
      cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₂) S.g := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [Category.assoc, he, ← Category.assoc, tensorCubeLowMixed0Partial_inclusion,
    Category.assoc]
  simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp, zero_comp]
  exact tensorCubeFirstLayerInclusion_pair2 S.g

/-- Extract the DAA mixed component by lifting once more in the third position. -/
def tensorCubeLowMixed0 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₁ S σ
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeLowMixed0Partial S hS hproj) (by
    have hz := tensorCubeLowMixed0Partial_quotient_zero S hS hproj
    simp only [cochainTensorTripleMap, cochainTensorMap_id] at hz
    exact hz)

@[reassoc]
lemma tensorCubeLowMixed0_third_inclusion :
    tensorCubeLowMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f =
      tensorCubeLowMixed0Partial S hS hproj := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  dsimp [tensorCubeLowMixed0]
  exact Fork.IsLimit.lift_ι _

@[reassoc]
lemma tensorCubeLowMixed0_inclusion :
    tensorCubeLowMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) S.f S.f =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) := by
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [← he, ← Category.assoc, tensorCubeLowMixed0_third_inclusion,
    tensorCubeLowMixed0Partial_inclusion]

include hS hproj in
lemma tensorCubeLowMixed0_target_inclusion_mono :
    Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have h2 := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₂
  have h3 := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₁ S σ
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂)) := h2.mono_f
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f) := by
    rw [cochainTensorTripleMap, cochainTensorMap_id]
    exact h3.mono_f
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed0 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed0 S hS hproj = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f)).mp
  rw [Category.assoc, tensorCubeLowMixed0_inclusion,
    tensorCubeFirstLayerFirstMap_inclusion_assoc]
  simp only [tensorCubeMap, cochainTensorTripleMap, cochainTensorMap_comp,
    S.zero, comp_id, cochainTensorMap_zero_left, zero_comp]

attribute [reassoc] tensorCubeFirstLayerRotation_cube cochainTensorRotation_cube
attribute [reassoc] tensorCubeFirstLayerFirstMap_lowMixed0

/-- The ADA component is the transported first mixed quotient map. -/
def tensorCubeLowMixed1 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ :=
  tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerRotation S.g ≫
    tensorCubeLowMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom

/-- The AAD component is obtained by one rotation on the source and two on the target. -/
def tensorCubeLowMixed2 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃ :=
  tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj ≫
    (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom ≫
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed0 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj =
      tensorCubeLowMixed2 S hS hproj ≫ (cochainTensorRotationIso S.X₁ S.X₁ S.X₃).hom := by
  simp only [tensorCubeLowMixed2, Category.assoc, cochainTensorRotation_cube, comp_id]

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed1 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed1 S hS hproj =
      tensorCubeLowMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom := by
  simp only [tensorCubeLowMixed1, tensorCubeFirstLayerRotation_cube_assoc]

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed2 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed2 S hS hproj =
      tensorCubeLowMixed1 S hS hproj ≫ (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom := by
  simp only [tensorCubeLowMixed1, tensorCubeLowMixed2, Category.assoc]

/-- All three low mixed quotient maps combined. -/
def tensorCubeLowMixedMap : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ ⊞
      (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞
        cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) :=
  biprod.lift (tensorCubeLowMixed0 S hS hproj)
    (biprod.lift (tensorCubeLowMixed1 S hS hproj) (tensorCubeLowMixed2 S hS hproj))

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed1 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed1 S hS hproj = 0 := by
  change tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerRotation S.g ≫
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj ≫
      (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom = 0
  exact comp_twice_equivariant_zero _ _ _ _ _
    (tensorCubeFirstLayerFirstMap_rotation S) (tensorCubeFirstLayerFirstMap_lowMixed0 S hS hproj)

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed2 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed2 S hS hproj = 0 := by
  rw [tensorCubeLowMixed2, ← Category.assoc, tensorCubeFirstLayerFirstMap_rotation]
  simp only [Category.assoc]
  rw [tensorCubeFirstLayerFirstMap_lowMixed0_assoc S hS hproj]
  simp only [zero_comp, comp_zero]

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixedMap :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext
  · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_fst, zero_comp,
      tensorCubeFirstLayerFirstMap_lowMixed0]
  · apply biprod.hom_ext
    · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_snd_assoc,
        biprod.lift_fst, zero_comp, tensorCubeFirstLayerFirstMap_lowMixed1]
    · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_snd,
        zero_comp, tensorCubeFirstLayerFirstMap_lowMixed2]

abbrev tensorCubeLowMixedShortComplex :=
  ShortComplex.mk (tensorCubeFirstLayerFirstMap S) (tensorCubeLowMixedMap S hS hproj)
    (tensorCubeFirstLayerFirstMap_lowMixedMap S hS hproj)

end Adams
end SerrePositivity

end TensorCubeLowMixedPart

section TensorCubeLowMixedInclusionsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

attribute [reassoc] tensorCubeRotation_cube

@[reassoc]
lemma tensorCubeLowMixed1_inclusion :
    tensorCubeLowMixed1 S hS hproj ≫ cochainTensorTripleMap S.f (𝟙 S.X₃) S.f =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap (𝟙 S.X₂) S.g (𝟙 S.X₂) := by
  simp only [tensorCubeLowMixed1, Category.assoc]
  rw [← cochainTensorRotation_naturality (𝟙 S.X₃) S.f S.f,
    ← Category.assoc (tensorCubeLowMixed0 S hS hproj), tensorCubeLowMixed0_inclusion]
  simp only [Category.assoc]
  have hs : CommSq (tensorCubeFirstLayerRotation S.g) (tensorCubeFirstLayerInclusion S.g)
      (tensorCubeFirstLayerInclusion S.g) (tensorCubeRotation S.X₂) :=
    ⟨tensorCubeFirstLayerRotation_inclusion S.g⟩
  have hi := (hs.horiz_comp hs).w
  have hh : tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerRotation S.g ≫
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom =
      tensorCubeFirstLayerInclusion S.g ≫ tensorCubeRotation S.X₂ ≫ tensorCubeRotation S.X₂ ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom := by
    simpa only [Category.assoc] using hi =≫
      (cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom)
  refine hh.trans ?_
  rw [cochainTensorRotation_naturality S.g (𝟙 S.X₂) (𝟙 S.X₂)]
  simp only [tensorCubeRotation_cube_assoc]

set_option maxHeartbeats 400000 in
-- Two transported rotations require comparisons of iterated tensor and kernel instances.
@[reassoc]
lemma tensorCubeLowMixed2_inclusion :
    tensorCubeLowMixed2 S hS hproj ≫ cochainTensorTripleMap S.f S.f (𝟙 S.X₃) =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap (𝟙 S.X₂) (𝟙 S.X₂) S.g := by
  simp only [tensorCubeLowMixed2, Category.assoc]
  rw [← cochainTensorRotation_naturality S.f (𝟙 S.X₃) S.f,
    ← cochainTensorRotation_naturality_assoc (𝟙 S.X₃) S.f S.f,
    ← Category.assoc (tensorCubeLowMixed0 S hS hproj), tensorCubeLowMixed0_inclusion]
  simp only [Category.assoc]
  have hi := tensorCubeFirstLayerRotation_inclusion S.g
  have hh : tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerInclusion S.g ≫
      cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
      (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom =
      tensorCubeFirstLayerInclusion S.g ≫ tensorCubeRotation S.X₂ ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom := by
    simpa only [Category.assoc] using hi =≫
      (cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom)
  refine hh.trans ?_
  rw [cochainTensorRotation_naturality_assoc S.g (𝟙 S.X₂) (𝟙 S.X₂),
    cochainTensorRotation_naturality (𝟙 S.X₂) S.g (𝟙 S.X₂)]
  simp only [tensorCubeRotation_cube_assoc]

include hS hproj in
lemma tensorCubeLowMixed1_target_inclusion_mono :
    Mono (cochainTensorTripleMap S.f (𝟙 S.X₃) S.f) := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  have he := cochainTensorRotation_naturality (𝟙 S.X₃) S.f S.f
  have hh : (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).inv ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom =
      cochainTensorTripleMap S.f (𝟙 S.X₃) S.f := by
    rw [he]
    simp only [Iso.inv_hom_id_assoc]
  rw [← hh]
  infer_instance

include hS hproj in
lemma tensorCubeLowMixed2_target_inclusion_mono :
    Mono (cochainTensorTripleMap S.f S.f (𝟙 S.X₃)) := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  have he := cochainTensorRotation_naturality S.f (𝟙 S.X₃) S.f
  have hh : (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).inv ≫
      cochainTensorTripleMap S.f (𝟙 S.X₃) S.f ≫
      (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom =
      cochainTensorTripleMap S.f S.f (𝟙 S.X₃) := by
    rw [he]
    simp only [Iso.inv_hom_id_assoc]
  rw [← hh]
  infer_instance

end Adams
end SerrePositivity

end TensorCubeLowMixedInclusionsPart

section TensorCubeLowMixedSectionsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorCubeLowMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) :=
  cochainShortComplex_f_g S

/-- Lift a DAA component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap (cochainSplittingSection S σ) S.f.f S.f.f n

lemma tensorCubeLowMixedRawSection0X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection0X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

/-- The DAA graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection0X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection0X S σ n)
    (tensorCubeLowMixedRawSection0X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection0X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection0X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift a ADA component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap S.f.f (cochainSplittingSection S σ) S.f.f n

lemma tensorCubeLowMixedRawSection1X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection1X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

/-- The ADA graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection1X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection1X S σ n)
    (tensorCubeLowMixedRawSection1X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection1X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection1X S σ n := cochainKernelLiftX_inclusion _ _ _ _

/-- Lift a AAD component into the cube using the degreewise quotient section. -/
def tensorCubeLowMixedRawSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n ⟶ (tensorCube S.X₂).X n :=
  cochainTensorTripleDegreeMap S.f.f S.f.f (cochainSplittingSection S σ) n

lemma tensorCubeLowMixedRawSection2X_pairMap_zero (n : ℤ) :
    tensorCubeLowMixedRawSection2X S σ n ≫ (tensorCubePairMap S.g).f n = 0 := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₃) S.X₂)
    (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃ ⊞
      cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst,
      ← cochainTensorTripleDegreeMap_eq S.g S.g (𝟙 S.X₂) n]
    simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
      tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₂ S.X₃) S.X₃)
      (cochainTensor (cochainTensor S.X₃ S.X₂) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst,
        ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g S.g n]
      simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd,
        ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) S.g n]
      simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
        tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

/-- The AAD graded component belongs to the first intermediate kernel. -/
def tensorCubeLowMixedSection2X (n : ℤ) :
    (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n (tensorCubeLowMixedRawSection2X S σ n)
    (tensorCubeLowMixedRawSection2X_pairMap_zero S σ n)

@[reassoc]
lemma tensorCubeLowMixedSection2X_inclusion (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowMixedRawSection2X S σ n := cochainKernelLiftX_inclusion _ _ _ _

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixedSection0X_component0 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed0_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  rw [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f S.f n

lemma tensorCubeLowMixedSection0X_component1 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed1_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeLowMixedSection0X_component2 (n : ℤ) :
    tensorCubeLowMixedSection0X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed2_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  simp only [tensorCubeLowMixedRawSection0X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeLowMixedSection1X_component0 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed0_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeLowMixedSection1X_component1 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed1_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  rw [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) S.f n

lemma tensorCubeLowMixedSection1X_component2 (n : ℤ) :
    tensorCubeLowMixedSection1X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed2_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  simp only [tensorCubeLowMixedRawSection1X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_third, zero_comp]

lemma tensorCubeLowMixedSection2X_component0 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed0 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed0_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_first, zero_comp]

lemma tensorCubeLowMixedSection2X_component1 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed1 S hS hproj).f n = 0 := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed1_inclusion S hS hproj)
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n]
  simp only [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp,
    tensorCubeLowMixedSplitting_f_g, cochainTensorTripleDegreeMap_zero_second, zero_comp]

lemma tensorCubeLowMixedSection2X_component2 (n : ℤ) :
    tensorCubeLowMixedSection2X S σ n ≫ (tensorCubeLowMixed2 S hS hproj).f n = 𝟙 _ := by
  have := tensorCubeLowMixed2_target_inclusion_mono S hS hproj
  apply cochainKernelLiftX_comp_eq (tensorCubeLowMixed2_inclusion S hS hproj)
  rw [id_comp, ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n]
  rw [tensorCubeLowMixedRawSection2X, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  rw [cochainSplitting_s_g]
  exact cochainTensorTripleDegreeMap_eq S.f S.f (𝟙 S.X₃) n

abbrev tensorCubeLowMixedTarget :=
  cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ ⊞
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞ cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃)

abbrev tensorCubeLowMixedProjection0X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).X n :=
  (biprod.fst : tensorCubeLowMixedTarget S ⟶ cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁).f n

abbrev tensorCubeLowMixedProjection1X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).X n :=
  ((biprod.snd ≫ biprod.fst) : tensorCubeLowMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁).f n

abbrev tensorCubeLowMixedProjection2X (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).X n :=
  ((biprod.snd ≫ biprod.snd) : tensorCubeLowMixedTarget S ⟶
    cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃).f n

@[reassoc]
lemma tensorCubeLowMixedMap_projection0X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection0X S n =
      (tensorCubeLowMixed0 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_fst]

@[reassoc]
lemma tensorCubeLowMixedMap_projection1X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection1X S n =
      (tensorCubeLowMixed1 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_snd_assoc, biprod.lift_fst]

@[reassoc]
lemma tensorCubeLowMixedMap_projection2X (n : ℤ) :
    (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedProjection2X S n =
      (tensorCubeLowMixed2 S hS hproj).f n := by
  rw [← HomologicalComplex.comp_f, tensorCubeLowMixedMap, biprod.lift_snd_assoc, biprod.lift_snd]

/-- The three graded component lifts form a section of the combined mixed quotient. -/
def tensorCubeLowMixedSectionX (n : ℤ) :
    (tensorCubeLowMixedTarget S).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  tensorCubeLowMixedProjection0X S n ≫ tensorCubeLowMixedSection0X S σ n +
    tensorCubeLowMixedProjection1X S n ≫ tensorCubeLowMixedSection1X S σ n +
    tensorCubeLowMixedProjection2X S n ≫ tensorCubeLowMixedSection2X S σ n

set_option maxHeartbeats 600000 in
-- All three inverse equations compare evaluated biproduct and iterated kernel models.
lemma tensorCubeLowMixedSectionX_section (n : ℤ) :
    tensorCubeLowMixedSectionX S σ n ≫ (tensorCubeLowMixedMap S hS hproj).f n = 𝟙 _ := by
  apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁)
    (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞ cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) n
  · rw [Category.assoc, tensorCubeLowMixedMap_projection0X, id_comp]
    exact section_sum0 _ _ _ _ _ _ _
      (tensorCubeLowMixedSection0X_component0 S σ hS hproj n)
      (tensorCubeLowMixedSection1X_component0 S σ hS hproj n)
      (tensorCubeLowMixedSection2X_component0 S σ hS hproj n)
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁)
      (cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeLowMixedMap_projection1X]
      simp only [id_comp]
      exact section_sum1 _ _ _ _ _ _ _
        (tensorCubeLowMixedSection0X_component1 S σ hS hproj n)
        (tensorCubeLowMixedSection1X_component1 S σ hS hproj n)
        (tensorCubeLowMixedSection2X_component1 S σ hS hproj n)
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        tensorCubeLowMixedMap_projection2X]
      simp only [id_comp]
      exact section_sum2 _ _ _ _ _ _ _
        (tensorCubeLowMixedSection0X_component2 S σ hS hproj n)
        (tensorCubeLowMixedSection1X_component2 S σ hS hproj n)
        (tensorCubeLowMixedSection2X_component2 S σ hS hproj n)

omit σ in
lemma tensorCubeLowMixedMap_epi : Epi (tensorCubeLowMixedMap S hS hproj) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  apply HomologicalComplex.epi_of_epi_f
  intro n
  exact epi_of_epi_fac (tensorCubeLowMixedSectionX_section S σ hS hproj n)

end Adams
end SerrePositivity

end TensorCubeLowMixedSectionsPart

section TensorCubeLowMixedRotationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

abbrev tensorCubeLowMixedRotation : tensorCubeLowMixedTarget S ⟶ tensorCubeLowMixedTarget S :=
  cochainTensorCyclicSumRotation S.X₃ S.X₁ S.X₁

abbrev tensorCubeLowMixedAction : CochainCubicAction (tensorCubeLowMixedTarget S) :=
  cochainTensorCyclicSumAction S.X₃ S.X₁ S.X₁

set_option maxHeartbeats 600000 in
-- Compare the combined maps through the evaluated nested-kernel and biproduct models.
lemma tensorCubeLowMixedMap_rotation (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixedMap S hS hproj =
      tensorCubeLowMixedMap S hS hproj ≫ tensorCubeLowMixedRotation S := by
  exact three_components_rotation (tensorCubeFirstLayerRotation S.g)
    (tensorCubeLowMixed0 S hS hproj) (tensorCubeLowMixed1 S hS hproj)
    (tensorCubeLowMixed2 S hS hproj) (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₁ S.X₃).hom
    (tensorCubeFirstLayerRotation_lowMixed0 S hS hproj)
    (tensorCubeFirstLayerRotation_lowMixed1 S hS hproj)
    (tensorCubeFirstLayerRotation_lowMixed2 S hS hproj)

end Adams
end SerrePositivity

end TensorCubeLowMixedRotationPart

section TensorCubeLowMixedReconstructionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

/-- Retract onto AAA by the degreewise retraction in all three positions. -/
def tensorCubeLowMixedRetractionX (n : ℤ) :
    (tensorCubeFirstLayer S.g).X n ⟶ (tensorCube S.X₁).X n :=
  (tensorCubeFirstLayerInclusion S.g).f n ≫
    cochainTensorTripleDegreeMap (cochainSplittingRetraction S σ)
      (cochainSplittingRetraction S σ) (cochainSplittingRetraction S σ) n

lemma tensorCubeLowMixedRetractionX_retract (n : ℤ) :
    (tensorCubeFirstLayerFirstMap S).f n ≫ tensorCubeLowMixedRetractionX S σ n = 𝟙 _ := by
  rw [tensorCubeLowMixedRetractionX, ← HomologicalComplex.comp_f_assoc,
    tensorCubeFirstLayerFirstMap_inclusion,
    ← cochainTensorTripleDegreeMap_eq S.f S.f S.f n, cochainTensorTripleDegreeMap_comp]
  have he : (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) =
      (fun i => 𝟙 (S.X₁.X i)) := funext fun i => (σ i).f_r
  rw [he, cochainTensorTripleDegreeMap_id]

lemma tensorCubeLowMixedRetractionX_first_inclusion (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫
      cochainTensorTripleDegreeMap (tensorCubeSplittingA S σ)
        (tensorCubeSplittingA S σ) (tensorCubeSplittingA S σ) n := by
  rw [← HomologicalComplex.comp_f, tensorCubeFirstLayerFirstMap_inclusion,
    tensorCubeLowMixedRetractionX, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq S.f S.f S.f n, cochainTensorTripleDegreeMap_comp]

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixed0_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed0 S hS hproj).f n ≫ tensorCubeLowMixedSection0X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (tensorCubeSplittingB S σ) (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorCubeLowMixedSection0X_inclusion]
  have he : tensorCubeLowMixedRawSection0X S σ n =
      (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f).f n ≫
        cochainTensorTripleDegreeMap (cochainSplittingSection S σ)
          (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f S.f n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection0X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed0_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

lemma tensorCubeLowMixed1_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed1 S hS hproj).f n ≫ tensorCubeLowMixedSection1X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (fun i => 𝟙 (S.X₂.X i)) (tensorCubeSplittingB S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorCubeLowMixedSection1X_inclusion]
  have he : tensorCubeLowMixedRawSection1X S σ n =
      (cochainTensorTripleMap S.f (𝟙 S.X₃) S.f).f n ≫
        cochainTensorTripleDegreeMap (fun i => 𝟙 (S.X₂.X i))
          (cochainSplittingSection S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) S.f n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection1X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed1_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

lemma tensorCubeLowMixed2_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed2 S hS hproj).f n ≫ tensorCubeLowMixedSection2X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) (tensorCubeSplittingB S σ) n := by
  rw [tensorCubeLowMixedSection2X_inclusion]
  have he : tensorCubeLowMixedRawSection2X S σ n =
      (cochainTensorTripleMap S.f S.f (𝟙 S.X₃)).f n ≫
        cochainTensorTripleDegreeMap (fun i => 𝟙 (S.X₂.X i))
          (fun i => 𝟙 (S.X₂.X i)) (cochainSplittingSection S σ) n := by
    rw [← cochainTensorTripleDegreeMap_eq S.f S.f (𝟙 S.X₃) n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection2X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed2_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

/-- AAA and the three low mixed components reconstruct the first intermediate layer. -/
lemma tensorCubeLowMixedSplitting_total (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixed0 S hS hproj).f n ≫ tensorCubeLowMixedSection0X S σ n +
      (tensorCubeLowMixed1 S hS hproj).f n ≫ tensorCubeLowMixedSection1X S σ n +
      (tensorCubeLowMixed2 S hS hproj).f n ≫ tensorCubeLowMixedSection2X S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n) := by
  apply (cancel_mono ((tensorCubeFirstLayerInclusion S.g).f n)).mp
  rw [add_comp, add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, tensorCubeLowMixedRetractionX_first_inclusion,
    tensorCubeLowMixed0_section_inclusion, tensorCubeLowMixed1_section_inclusion,
    tensorCubeLowMixed2_section_inclusion, id_comp]
  exact tensorCubeFirstLayerInclusion_sparse S.g (tensorCubeSplittingA S σ)
    (cochainSplittingSection S σ) (funext fun i => (σ i).id) n

end Adams
end SerrePositivity

end TensorCubeLowMixedReconstructionPart

section TensorCubeLowMixedExactPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams

private lemma three_component_total {C : Type*} [Category C] [Preadditive C]
    {A K Y Y₀ Y₁ Y₂ : C} (r : K ⟶ A) (f : A ⟶ K) (g : K ⟶ Y)
    (p₀ : Y ⟶ Y₀) (p₁ : Y ⟶ Y₁) (p₂ : Y ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K)
    (m₀ : K ⟶ Y₀) (m₁ : K ⟶ Y₁) (m₂ : K ⟶ Y₂)
    (h₀ : g ≫ p₀ = m₀) (h₁ : g ≫ p₁ = m₁) (h₂ : g ≫ p₂ = m₂)
    (ht : r ≫ f + m₀ ≫ d₀ + m₁ ≫ d₁ + m₂ ≫ d₂ = 𝟙 K) :
    r ≫ f + g ≫ (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) = 𝟙 K := by
  rw [comp_add, comp_add, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    h₀, h₁, h₂, ← add_assoc, ← add_assoc]
  exact ht

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixedSplitting_identity
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedSectionX S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n) := by
  exact three_component_total
    (tensorCubeLowMixedRetractionX S σ n) ((tensorCubeFirstLayerFirstMap S).f n)
    ((tensorCubeLowMixedMap S hS hproj).f n)
    (tensorCubeLowMixedProjection0X S n) (tensorCubeLowMixedProjection1X S n)
    (tensorCubeLowMixedProjection2X S n)
    (tensorCubeLowMixedSection0X S σ n) (tensorCubeLowMixedSection1X S σ n)
    (tensorCubeLowMixedSection2X S σ n)
    ((tensorCubeLowMixed0 S hS hproj).f n) ((tensorCubeLowMixed1 S hS hproj).f n)
    ((tensorCubeLowMixed2 S hS hproj).f n)
    (tensorCubeLowMixedMap_projection0X S hS hproj n)
    (tensorCubeLowMixedMap_projection1X S hS hproj n)
    (tensorCubeLowMixedMap_projection2X S hS hproj n)
    (tensorCubeLowMixedSplitting_total S σ hS hproj n)

set_option maxHeartbeats 600000 in
-- Evaluation of the nested-kernel sequence needs normalization of its three structure fields.
/-- The low mixed short complex splits in every degree. -/
def tensorCubeLowMixedSplitting
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    ((tensorCubeLowMixedShortComplex S hS hproj).map (eval _ _ n)).Splitting where
  r := tensorCubeLowMixedRetractionX S σ n
  s := tensorCubeLowMixedSectionX S σ n
  f_r := tensorCubeLowMixedRetractionX_retract S σ n
  s_g := tensorCubeLowMixedSectionX_section S σ hS hproj n
  id := by
    change tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedSectionX S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n)
    exact tensorCubeLowMixedSplitting_identity S hS hproj σ n

lemma tensorCubeLowMixedShortComplex_shortExact :
    (tensorCubeLowMixedShortComplex S hS hproj).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
    (tensorCubeLowMixedSplitting S hS hproj
      (cochainDegreewiseSplittingOfProjective S hS hproj) n).shortExact)

set_option maxHeartbeats 600000 in
set_option maxHeartbeats 600000 in
end Adams
end SerrePositivity

end TensorCubeLowMixedExactPart

section TensorCubeLowMixedSupportPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

lemma tensorCubeLowMixedTarget_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeLowMixedTarget S) := by
  exact strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _
      (strictlyPerfectComplex_cochainTensor _ _ hd ha) ha)
    (strictlyPerfectComplex_biprod
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ ha hd) ha)
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ ha ha) hd))

lemma tensorCubeLowMixedTarget_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeLowMixedTarget S) := by
  exact ((hsD.cochainTensor_left hd S.X₁).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ hd ha) S.X₁).biprod
    (((hsA.cochainTensor_left ha S.X₃).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ ha hd) S.X₁).biprod
      ((hsA.cochainTensor_left ha S.X₁).cochainTensor_left
        (strictlyPerfectComplex_cochainTensor _ _ ha ha) S.X₃))

lemma tensorCubeFirstLayer_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeFirstLayer S.g) := by
  have hT := tensorCubeLowMixedShortComplex_shortExact S hS (fun i => (hd.2 i).2)
  intro n
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hT.homology_exact₂ n)
  exact (module_support_subset_union_of_exact _ _ he).trans
    (Set.union_subset (tensorCube_support ha hsA n)
      (tensorCubeLowMixedTarget_support S ha hd hsA hsD n))

end Adams
end SerrePositivity

end TensorCubeLowMixedSupportPart
