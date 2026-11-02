module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.CochainTensor.DegreeMaps
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.HomologicalAlgebra.CochainTensor.ShortExact
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare
public import SerrePositivity.PerfectComplex.Eigen.Involution
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # テンソル二乗のフィルトレーション

## 概要

短完全列のテンソル二乗のフィルトレーションの中間の層と、混合成分への標準的な写像、混合列の次数ごとの分裂、正と負の混合成分の打ち消しを与える。

## 方針

混合成分は二つの因子の入れ替えで対になり、正と負の差で打ち消し合う。

## 規約

次数ごとの分裂は HomologicalAlgebra/CochainTensor/DegreeMaps による。

## 使われ方

`TensorPower/TensorSquareClass`（加法性）。
-/

@[expose] public noncomputable section

universe u

section TensorSquareFiltrationPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The intermediate layer consists of tensors with at least one factor in the kernel. -/
abbrev tensorSquareKernel (q : P ⟶ D) := kernel (tensorSquareMap q)

abbrev tensorSquareKernelInclusion (q : P ⟶ D) : tensorSquareKernel q ⟶ tensorSquare P :=
  kernel.ι (tensorSquareMap q)

/-- Signed exchange preserves the intermediate layer. -/
def tensorSquareKernelSwap (q : P ⟶ D) : tensorSquareKernel q ⟶ tensorSquareKernel q :=
  kernel.lift (tensorSquareMap q) (tensorSquareKernelInclusion q ≫ tensorSquareSwap P) (by
    rw [Category.assoc, ← tensorSquareSwap_naturality, ← Category.assoc,
      kernel.condition, zero_comp])

@[simp, reassoc]
lemma tensorSquareKernelSwap_inclusion (q : P ⟶ D) :
    tensorSquareKernelSwap q ≫ tensorSquareKernelInclusion q =
      tensorSquareKernelInclusion q ≫ tensorSquareSwap P := kernel.lift_ι _ _ _

lemma tensorSquareKernelSwap_sq (q : P ⟶ D) :
    tensorSquareKernelSwap q ≫ tensorSquareKernelSwap q = 𝟙 _ := by
  apply (cancel_mono (tensorSquareKernelInclusion q)).1
  simp only [Category.assoc, tensorSquareKernelSwap_inclusion,
    tensorSquareKernelSwap_inclusion_assoc, tensorSquareSwap_sq, comp_id, id_comp]

def tensorSquareKernelInvolution (q : P ⟶ D) : CochainInvolution (tensorSquareKernel q) :=
  ⟨tensorSquareKernelSwap q, tensorSquareKernelSwap_sq q⟩

abbrev tensorSquareKernelShortComplex (q : P ⟶ D) :=
  ShortComplex.mk (tensorSquareKernelInclusion q) (tensorSquareMap q) (kernel.condition _)

lemma tensorSquareMap_epi_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Epi (tensorSquareMap S.g) := by
  have hr := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₂
  have hl := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Epi (cochainTensorMap S.g (𝟙 S.X₂)) := hr.epi_g
  have : Epi (cochainTensorMap (𝟙 S.X₃) S.g) := hl.epi_g
  have he : cochainTensorMap S.g (𝟙 S.X₂) ≫ cochainTensorMap (𝟙 S.X₃) S.g =
      tensorSquareMap S.g := by
    rw [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorSquareKernelShortComplex_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    (tensorSquareKernelShortComplex S.g).ShortExact := by
  have := tensorSquareMap_epi_of_shortExact S hS hproj
  exact { exact := ShortComplex.exact_kernel (tensorSquareMap S.g) }

lemma tensorSquareKernel_perfect
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorSquareKernel S.g) :=
  strictlyPerfectComplex_of_shortExact (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorSquare_perfect S.X₂ hp) (fun i => ((tensorSquare_perfect S.X₃ hd).2 i).2)

lemma tensorSquareKernel_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃)
    (hsP : HasHomologySupportOn Z S.X₂) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorSquareKernel S.g) :=
  HasHomologySupportOn.of_shortExact (tensorSquareKernelShortComplex S.g)
    (tensorSquareKernelShortComplex_shortExact S hS (fun i => (hd.2 i).2))
    (tensorSquare_support hp hsP) (tensorSquare_support hd hsD)

/-- The tensor square of the first term maps into the intermediate layer. -/
def tensorSquareKernelFirstMap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquare S.X₁ ⟶ tensorSquareKernel S.g :=
  kernel.lift (tensorSquareMap S.g) (tensorSquareMap S.f) (by
    rw [cochainTensorMap_comp, S.zero, cochainTensorMap_zero_zero])

@[simp, reassoc]
lemma tensorSquareKernelFirstMap_inclusion
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquareKernelFirstMap S ≫ tensorSquareKernelInclusion S.g = tensorSquareMap S.f :=
  kernel.lift_ι _ _ _

lemma tensorSquareMap_mono_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorSquareMap S.f) := by
  have hr := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₁
  have hl := cochainTensorShortComplexLeft_shortExact_of_projective S.X₂ S hS hproj
  have : Mono (cochainTensorMap S.f (𝟙 S.X₁)) := hr.mono_f
  have : Mono (cochainTensorMap (𝟙 S.X₂) S.f) := hl.mono_f
  have he : cochainTensorMap S.f (𝟙 S.X₁) ≫ cochainTensorMap (𝟙 S.X₂) S.f =
      tensorSquareMap S.f := by
    rw [cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

lemma tensorSquareKernelFirstMap_mono
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) : Mono (tensorSquareKernelFirstMap S) := by
  have := tensorSquareMap_mono_of_shortExact S hS hproj
  exact mono_of_mono_fac (tensorSquareKernelFirstMap_inclusion S)

@[reassoc]
lemma tensorSquareKernelFirstMap_swap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    tensorSquareKernelFirstMap S ≫ tensorSquareKernelSwap S.g =
      tensorSquareSwap S.X₁ ≫ tensorSquareKernelFirstMap S := by
  apply (cancel_mono (tensorSquareKernelInclusion S.g)).1
  simp only [Category.assoc, tensorSquareKernelSwap_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, tensorSquareKernelFirstMap_inclusion]
  exact tensorSquareSwap_naturality S.f

end Adams
end SerrePositivity

end TensorSquareFiltrationPart

section TensorSquareMixedPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
  (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract the `A ⊗ D` component by the universal property of the tensor kernel. -/
def tensorSquareMixedLeft : tensorSquareKernel S.g ⟶ cochainTensor S.X₁ S.X₃ := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have := hT.mono_f
  exact hT.exact.lift
    (tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g) (by
      change (tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g) ≫
        cochainTensorMap S.g (𝟙 S.X₃) = 0
      rw [Category.assoc, cochainTensorMap_comp, id_comp, comp_id, kernel.condition])

@[reassoc]
lemma tensorSquareMixedLeft_inclusion :
    tensorSquareMixedLeft S hS hproj ≫ cochainTensorMap S.f (𝟙 S.X₃) =
      tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g := by
  dsimp [tensorSquareMixedLeft]
  exact Fork.IsLimit.lift_ι _

/-- Extract the `D ⊗ A` component by the universal property of the other tensor kernel. -/
def tensorSquareMixedRight : tensorSquareKernel S.g ⟶ cochainTensor S.X₃ S.X₁ := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have := hT.mono_f
  exact hT.exact.lift
    (tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂)) (by
      change (tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂)) ≫
        cochainTensorMap (𝟙 S.X₃) S.g = 0
      rw [Category.assoc, cochainTensorMap_comp, comp_id, id_comp, kernel.condition])

@[reassoc]
lemma tensorSquareMixedRight_inclusion :
    tensorSquareMixedRight S hS hproj ≫ cochainTensorMap (𝟙 S.X₃) S.f =
      tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂) := by
  dsimp [tensorSquareMixedRight]
  exact Fork.IsLimit.lift_ι _

@[simp]
lemma tensorSquareKernelFirstMap_mixedLeft :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedLeft S hS hproj = 0 := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorMap S.f (𝟙 S.X₃))).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, cochainTensorMap_comp, comp_id, S.zero,
    cochainTensorMap_zero_right, zero_comp]

@[simp]
lemma tensorSquareKernelFirstMap_mixedRight :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedRight S hS hproj = 0 := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono (cochainTensorMap (𝟙 S.X₃) S.f)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, cochainTensorMap_comp, S.zero, comp_id,
    cochainTensorMap_zero_left, zero_comp]

/-- Exchange interchanges the two canonical mixed components with the Koszul symmetry. -/
@[reassoc]
lemma tensorSquareKernelSwap_mixedLeft :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedLeft S hS hproj =
      tensorSquareMixedRight S hS hproj ≫ (cochainTensorSymmetry S.X₃ S.X₁).hom := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorMap S.f (𝟙 S.X₃))).1
  calc
    _ = tensorSquareKernelSwap S.g ≫ tensorSquareKernelInclusion S.g ≫
        cochainTensorMap (𝟙 S.X₂) S.g := by
      rw [Category.assoc, tensorSquareMixedLeft_inclusion]
    _ = tensorSquareKernelInclusion S.g ≫ tensorSquareSwap S.X₂ ≫
        cochainTensorMap (𝟙 S.X₂) S.g := by rw [tensorSquareKernelSwap_inclusion_assoc]
    _ = tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂) ≫
        (cochainTensorSymmetry S.X₃ S.X₂).hom := by
      simpa only [Category.assoc] using
        tensorSquareKernelInclusion S.g ≫=
          (cochainTensorSymmetry_naturality S.g (𝟙 S.X₂)).symm
    _ = tensorSquareMixedRight S hS hproj ≫ cochainTensorMap (𝟙 S.X₃) S.f ≫
        (cochainTensorSymmetry S.X₃ S.X₂).hom := by
      simpa only [Category.assoc] using
        ((tensorSquareMixedRight_inclusion S hS hproj) =≫
          (cochainTensorSymmetry S.X₃ S.X₂).hom).symm
    _ = _ := by rw [cochainTensorSymmetry_naturality, Category.assoc]

@[reassoc]
lemma tensorSquareKernelSwap_mixedRight :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedRight S hS hproj =
      tensorSquareMixedLeft S hS hproj ≫ (cochainTensorSymmetry S.X₁ S.X₃).hom := by
  have h : tensorSquareKernelSwap S.g ≫ tensorSquareMixedLeft S hS hproj ≫
      (cochainTensorSymmetry S.X₁ S.X₃).hom = tensorSquareMixedRight S hS hproj := by
    rw [tensorSquareKernelSwap_mixedLeft_assoc, cochainTensorSymmetry_hom_comp, comp_id]
  rw [← h, ← Category.assoc, tensorSquareKernelSwap_sq, id_comp]

/-- The canonical map from the intermediate layer to the two mixed components. -/
def tensorSquareMixedMap : tensorSquareKernel S.g ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  biprod.lift (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj)

@[simp]
lemma tensorSquareKernelFirstMap_mixedMap :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext <;> simp [tensorSquareMixedMap]

/-- The inner short complex of the tensor-square filtration. -/
abbrev tensorSquareMixedShortComplex :=
  ShortComplex.mk (tensorSquareKernelFirstMap S) (tensorSquareMixedMap S hS hproj)
    (tensorSquareKernelFirstMap_mixedMap S hS hproj)

/-- The exchange on the two mixed components. -/
def tensorSquareMixedSwap : cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  biprod.desc ((cochainTensorSymmetry S.X₁ S.X₃).hom ≫ biprod.inr)
    ((cochainTensorSymmetry S.X₃ S.X₁).hom ≫ biprod.inl)

lemma tensorSquareMixedSwap_sq :
    tensorSquareMixedSwap S ≫ tensorSquareMixedSwap S = 𝟙 _ := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedSwap, Category.assoc] <;>
    simp [cochainTensorSymmetry_hom_comp]

lemma tensorSquareMixedMap_swap :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedMap S hS hproj =
      tensorSquareMixedMap S hS hproj ≫ tensorSquareMixedSwap S := by
  apply biprod.hom_ext <;>
    simp [tensorSquareMixedMap, tensorSquareMixedSwap, tensorSquareKernelSwap_mixedLeft,
      tensorSquareKernelSwap_mixedRight]

end Adams
end SerrePositivity

end TensorSquareMixedPart

section TensorSquareMixedSplittingPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
  (hproj : ∀ i, Module.Projective R (S.X₃.X i))
  (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorSquareMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) := by
  funext i
  exact congrArg (fun f => f.f i) S.zero

/-- The degreewise retraction onto the first tensor-square layer. -/
def tensorSquareMixedRetractionX (n : ℤ) : (tensorSquareKernel S.g).X n ⟶ (tensorSquare S.X₁).X n :=
  (tensorSquareKernelInclusion S.g).f n ≫
    cochainTensorDegreeMap (cochainSplittingRetraction S σ) (cochainSplittingRetraction S σ) n

lemma tensorSquareMixedRetractionX_retract (n : ℤ) :
    (tensorSquareKernelFirstMap S).f n ≫ tensorSquareMixedRetractionX S σ n = 𝟙 _ := by
  rw [tensorSquareMixedRetractionX, ← HomologicalComplex.comp_f_assoc,
    tensorSquareKernelFirstMap_inclusion]
  rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  have h : (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) =
      (fun i => 𝟙 (S.X₁.X i)) := funext fun i => (σ i).f_r
  rw [h, cochainTensorDegreeMap_id]

/-- A degreewise lift of the left mixed component into the intermediate layer. -/
def tensorSquareMixedSectionLeftX (n : ℤ) :
    (cochainTensor S.X₁ S.X₃).X n ⟶ (tensorSquareKernel S.g).X n := by
  have hT := tensorSquareKernelShortComplex_shortExact S hS hproj
  have := hT.mono_f
  have := hT.epi_g
  have hN := hT.map (eval _ _ n)
  have := hN.mono_f
  exact hN.exact.lift (cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n) (by
    change cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n ≫
      (tensorSquareMap S.g).f n = 0
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp,
      tensorSquareMixedSplitting_f_g, cochainTensorDegreeMap_zero_left])

@[reassoc]
lemma tensorSquareMixedSectionLeftX_inclusion (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareKernelInclusion S.g).f n =
      cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n := by
  dsimp [tensorSquareMixedSectionLeftX]
  exact Fork.IsLimit.lift_ι _

/-- A degreewise lift of the right mixed component into the intermediate layer. -/
def tensorSquareMixedSectionRightX (n : ℤ) :
    (cochainTensor S.X₃ S.X₁).X n ⟶ (tensorSquareKernel S.g).X n := by
  have hT := tensorSquareKernelShortComplex_shortExact S hS hproj
  have := hT.mono_f
  have := hT.epi_g
  have hN := hT.map (eval _ _ n)
  have := hN.mono_f
  exact hN.exact.lift (cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n) (by
    change cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n ≫
      (tensorSquareMap S.g).f n = 0
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp,
      tensorSquareMixedSplitting_f_g, cochainTensorDegreeMap_zero_right])

@[reassoc]
lemma tensorSquareMixedSectionRightX_inclusion (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareKernelInclusion S.g).f n =
      cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n := by
  dsimp [tensorSquareMixedSectionRightX]
  exact Fork.IsLimit.lift_ι _

@[reassoc]
lemma tensorSquareMixedLeft_inclusion_f (n : ℤ) :
    (tensorSquareMixedLeft S hS hproj).f n ≫ (cochainTensorMap S.f (𝟙 S.X₃)).f n =
      (tensorSquareKernelInclusion S.g).f n ≫ (cochainTensorMap (𝟙 S.X₂) S.g).f n :=
  congrArg (fun f => f.f n) (tensorSquareMixedLeft_inclusion S hS hproj)

@[reassoc]
lemma tensorSquareMixedRight_inclusion_f (n : ℤ) :
    (tensorSquareMixedRight S hS hproj).f n ≫ (cochainTensorMap (𝟙 S.X₃) S.f).f n =
      (tensorSquareKernelInclusion S.g).f n ≫ (cochainTensorMap S.g (𝟙 S.X₂)).f n :=
  congrArg (fun f => f.f n) (tensorSquareMixedRight_inclusion S hS hproj)

lemma tensorSquareMixedSectionLeftX_left (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareMixedLeft S hS hproj).f n =
      𝟙 _ := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap S.f (𝟙 S.X₃)).f n)).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion_f,
    tensorSquareMixedSectionLeftX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, id_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have h : (fun j => cochainSplittingSection S σ j ≫ S.g.f j) =
      (fun j => 𝟙 (S.X₃.X j)) := funext fun j => (σ j).s_g
  rw [h]
  exact cochainTensorDegreeMap_eq S.f (𝟙 S.X₃) n

lemma tensorSquareMixedSectionLeftX_right (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareMixedRight S hS hproj).f n =
      0 := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap (𝟙 S.X₃) S.f).f n)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion_f,
    tensorSquareMixedSectionLeftX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, tensorSquareMixedSplitting_f_g,
    cochainTensorDegreeMap_zero_left, zero_comp]

lemma tensorSquareMixedSectionRightX_left (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareMixedLeft S hS hproj).f n =
      0 := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap S.f (𝟙 S.X₃)).f n)).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion_f,
    tensorSquareMixedSectionRightX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, tensorSquareMixedSplitting_f_g,
    cochainTensorDegreeMap_zero_right, zero_comp]

lemma tensorSquareMixedSectionRightX_right (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareMixedRight S hS hproj).f n =
      𝟙 _ := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap (𝟙 S.X₃) S.f).f n)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion_f,
    tensorSquareMixedSectionRightX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, id_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have h : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [h]
  exact cochainTensorDegreeMap_eq (𝟙 S.X₃) S.f n

lemma tensorSquareMixedRetractionX_first_inclusion (n : ℤ) :
    tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i)
        (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i) n := by
  rw [← HomologicalComplex.comp_f, tensorSquareKernelFirstMap_inclusion,
    tensorSquareMixedRetractionX, Category.assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp]

lemma tensorSquareMixedLeft_section_inclusion (n : ℤ) :
    (tensorSquareMixedLeft S hS hproj).f n ≫ tensorSquareMixedSectionLeftX S hS hproj σ n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => 𝟙 (S.X₂.X i))
        (fun i => S.g.f i ≫ cochainSplittingSection S σ i) n := by
  rw [tensorSquareMixedSectionLeftX_inclusion]
  have he : cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n =
      (cochainTensorMap S.f (𝟙 S.X₃)).f n ≫
        cochainTensorDegreeMap (fun i => 𝟙 (S.X₂.X i)) (cochainSplittingSection S σ) n := by
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, tensorSquareMixedLeft_inclusion_f, Category.assoc,
    ← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]

lemma tensorSquareMixedRight_section_inclusion (n : ℤ) :
    (tensorSquareMixedRight S hS hproj).f n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => S.g.f i ≫ cochainSplittingSection S σ i)
        (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorSquareMixedSectionRightX_inclusion]
  have he : cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n =
      (cochainTensorMap (𝟙 S.X₃) S.f).f n ≫
        cochainTensorDegreeMap (cochainSplittingSection S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, tensorSquareMixedRight_inclusion_f, Category.assoc,
    ← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]

lemma tensorSquareMixed_doubleQuotient_zero (n : ℤ) :
    (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => S.g.f i ≫ cochainSplittingSection S σ i)
        (fun i => S.g.f i ≫ cochainSplittingSection S σ i) n = 0 := by
  rw [← cochainTensorDegreeMap_comp, cochainTensorDegreeMap_eq S.g S.g n,
    ← Category.assoc, ← HomologicalComplex.comp_f, kernel.condition]
  simp

/-- The first and two mixed components reconstruct every element of the intermediate layer. -/
lemma tensorSquareMixedSplitting_total (n : ℤ) :
    tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n +
      (tensorSquareMixedLeft S hS hproj).f n ≫
    tensorSquareMixedSectionLeftX S hS hproj σ n +
      (tensorSquareMixedRight S hS hproj).f n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n =
      𝟙 ((tensorSquareKernel S.g).X n) := by
  apply (cancel_mono ((tensorSquareKernelInclusion S.g).f n)).1
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc,
    tensorSquareMixedRetractionX_first_inclusion, tensorSquareMixedLeft_section_inclusion,
    tensorSquareMixedRight_section_inclusion, id_comp, ← comp_add, ← comp_add]
  have h : (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i +
      S.g.f i ≫ cochainSplittingSection S σ i) = (fun i => 𝟙 (S.X₂.X i)) :=
    funext fun i => (σ i).id
  rw [cochainTensorDegreeMap_partition _ _ h, comp_add, comp_id,
    tensorSquareMixed_doubleQuotient_zero, add_zero]

abbrev cochainBiprodFstX (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (A ⊞ B).X n ⟶ A.X n := (biprod.fst : A ⊞ B ⟶ A).f n

abbrev cochainBiprodSndX (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (A ⊞ B).X n ⟶ B.X n := (biprod.snd : A ⊞ B ⟶ B).f n

lemma cochainBiprodX_hom_ext
    (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) {W : ModuleCat.{u} R}
    (f g : W ⟶ (A ⊞ B).X n)
    (hf : f ≫ (biprod.fst : A ⊞ B ⟶ A).f n = g ≫ cochainBiprodFstX A B n)
    (hg : f ≫ (biprod.snd : A ⊞ B ⟶ B).f n = g ≫ cochainBiprodSndX A B n) : f = g := by
  apply (isLimitOfPreserves (eval (ModuleCat.{u} R) (.up ℤ) n)
    (BinaryBiproduct.isLimit A B)).hom_ext
  rintro ⟨j⟩
  cases j
  · exact hf
  · exact hg

@[reassoc]
lemma tensorSquareMixedMap_fst_f (n : ℤ) :
    (tensorSquareMixedMap S hS hproj).f n ≫
      cochainBiprodFstX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n =
      (tensorSquareMixedLeft S hS hproj).f n :=
  congrArg (fun f => f.f n) (biprod.lift_fst
    (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj))

@[reassoc]
lemma tensorSquareMixedMap_snd_f (n : ℤ) :
    (tensorSquareMixedMap S hS hproj).f n ≫
      cochainBiprodSndX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n =
      (tensorSquareMixedRight S hS hproj).f n :=
  congrArg (fun f => f.f n) (biprod.lift_snd
    (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj))

/-- The two component lifts combine into a degreewise section of the mixed map. -/
def tensorSquareMixedSectionX (n : ℤ) :
    (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁).X n ⟶ (tensorSquareKernel S.g).X n :=
  cochainBiprodFstX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n ≫
    tensorSquareMixedSectionLeftX S hS hproj σ n +
    cochainBiprodSndX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n

lemma tensorSquareMixedSectionX_section (n : ℤ) :
    tensorSquareMixedSectionX S hS hproj σ n ≫ (tensorSquareMixedMap S hS hproj).f n = 𝟙 _ := by
  apply cochainBiprodX_hom_ext (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n
  · rw [Category.assoc, tensorSquareMixedMap_fst_f, tensorSquareMixedSectionX,
      add_comp, Category.assoc, Category.assoc, tensorSquareMixedSectionLeftX_left,
      tensorSquareMixedSectionRightX_left, comp_id, comp_zero, add_zero, id_comp]
  · rw [Category.assoc, tensorSquareMixedMap_snd_f, tensorSquareMixedSectionX,
      add_comp, Category.assoc, Category.assoc, tensorSquareMixedSectionLeftX_right,
      tensorSquareMixedSectionRightX_right, comp_zero, comp_id, zero_add, id_comp]

/-- The inner mixed sequence splits in each degree. -/
def tensorSquareMixedSplitting (n : ℤ) :
    ((tensorSquareMixedShortComplex S hS hproj).map (eval _ _ n)).Splitting where
  r := tensorSquareMixedRetractionX S σ n
  s := tensorSquareMixedSectionX S hS hproj σ n
  f_r := tensorSquareMixedRetractionX_retract S σ n
  s_g := tensorSquareMixedSectionX_section S hS hproj σ n
  id := by
    change tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n +
      (tensorSquareMixedMap S hS hproj).f n ≫ tensorSquareMixedSectionX S hS hproj σ n =
      𝟙 ((tensorSquareKernel S.g).X n)
    rw [tensorSquareMixedSectionX, comp_add, ← Category.assoc, ← Category.assoc,
      tensorSquareMixedMap_fst_f, tensorSquareMixedMap_snd_f, ← add_assoc]
    exact tensorSquareMixedSplitting_total S hS hproj σ n

/-- The canonical inner sequence of the tensor-square filtration is short exact. -/
lemma tensorSquareMixedShortComplex_shortExact :
    (tensorSquareMixedShortComplex S hS hproj).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (tensorSquareMixedSplitting S hS hproj
      (cochainDegreewiseSplittingOfProjective S hS hproj) n).shortExact)

/-- The quotient of the intermediate layer by the first layer is the mixed complex. -/
def tensorSquareMixedCokernelIso : cokernel (tensorSquareKernelFirstMap S) ≅
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  (cokernelIsCokernel (tensorSquareKernelFirstMap S)).coconePointUniqueUpToIso
    (tensorSquareMixedShortComplex_shortExact S hS hproj).gIsCokernel

@[reassoc]
lemma tensorSquareMixedCokernelIso_π_hom :
    cokernel.π (tensorSquareKernelFirstMap S) ≫ (tensorSquareMixedCokernelIso S hS hproj).hom =
      tensorSquareMixedMap S hS hproj :=
  (cokernelIsCokernel (tensorSquareKernelFirstMap S)).comp_coconePointUniqueUpToIso_hom
    (tensorSquareMixedShortComplex_shortExact S hS hproj).gIsCokernel WalkingParallelPair.one

end Adams
end SerrePositivity

end TensorSquareMixedSplittingPart

section TensorSquareMixedCancellationPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

def tensorSquareMixedInvolution :
    CochainInvolution (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  ⟨tensorSquareMixedSwap S, tensorSquareMixedSwap_sq S⟩

/-- Negate the second mixed component and preserve the first. -/
def tensorSquareMixedGrading : cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ := biprod.map (𝟙 _) (-𝟙 _)

lemma tensorSquareMixedGrading_sq :
    tensorSquareMixedGrading S ≫ tensorSquareMixedGrading S = 𝟙 _ := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedGrading, Category.assoc]

lemma tensorSquareMixedGrading_anticommute :
    tensorSquareMixedSwap S ≫ tensorSquareMixedGrading S =
      -(tensorSquareMixedGrading S ≫ tensorSquareMixedSwap S) := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedSwap, tensorSquareMixedGrading, Category.assoc]

/-- The positive and negative mixed eigenspaces are chain isomorphic. -/
def tensorSquareMixedPositiveNegativeIso [Invertible (2 : R)] :
    (tensorSquareMixedInvolution S).positive.image ≅
      (tensorSquareMixedInvolution S).negative.image :=
  (tensorSquareMixedInvolution S).positiveNegativeIso (tensorSquareMixedGrading S)
    (tensorSquareMixedGrading_anticommute S) (tensorSquareMixedGrading_sq S)

lemma tensorSquareMixed_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _ ha hd)
    (strictlyPerfectComplex_cochainTensor _ _ hd ha)

lemma tensorSquareMixed_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁) :=
  (hsA.cochainTensor_left ha S.X₃).biprod (hsD.cochainTensor_left hd S.X₁)

lemma tensorSquareMixed_k0Class_eq_zero [Invertible (2 : R)]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    (tensorSquareMixedInvolution S).k0Class Z (tensorSquareMixed_perfect S ha hd)
      (tensorSquareMixed_support S ha hd hsA hsD) = 0 :=
  (tensorSquareMixedInvolution S).k0Class_eq_zero_of_anticommute Z
    (tensorSquareMixed_perfect S ha hd) (tensorSquareMixed_support S ha hd hsA hsD)
    (tensorSquareMixedGrading S) (tensorSquareMixedGrading_anticommute S)
    (tensorSquareMixedGrading_sq S)

end Adams
end SerrePositivity

end TensorSquareMixedCancellationPart
