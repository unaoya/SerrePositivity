module
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonLeftPath
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonRightPath
public import SerrePositivity.InfinityCategories.Derived.ActionPentagonTransfer
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositorCoherence
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionPentagon
/-!
概要：元の指定導来 kernel 合成子 κ の五角式を証明する。
方針：左右経路を同じ水平三重比較へ移し、同じ終辺の ξ 自然性と全前合成で反映する。
規約：三 kernel の右相対 K-flat 性を明示し、原 Hom の平坦性を追加しない。
使われ方：元の指定導来 kernel の coherence と一般 cell 模型への移送。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F] [DGCategory R G] [Small.{u} G]
private lemma compositor_comparison (P : Bimodule R E D) (Q : Bimodule R F E)
    (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P Q hP).precomp
        (dgRelativeKFlatResolution R D) ≪≫
      dgRelativeKFlatKernelNerve_derivedIso R D F (BimoduleTensor.compose R F E D Q P)
        (Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP) =
    comparisonCompositionIso (dgRelativeKFlatResolution R D) (dgRelativeKFlatResolution R E)
      (dgRelativeKFlatResolution R F) (dgKernelDerivedInfinity R D E P)
      (dgRelativeKFlatKernelNerve R D E P hP) (dgKernelDerivedInfinity R E F Q)
      (dgRelativeKFlatKernelNerve R E F Q hQ)
      (dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
      (dgRelativeKFlatKernelNerve_derivedIso R E F Q hQ) ≪≫
      (dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
        (dgRelativeKFlatResolution R F) := by
  simpa only [comparisonCompositionIso, Iso.trans_assoc] using!
    dgRelativeKFlatKernelCompositor_iso R D E F P Q hP hQ
variable (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F)
  (hP : Bimodule.rightRelativeKFlat R E D P) (hQ : Bimodule.rightRelativeKFlat R F E Q)
  (hS : Bimodule.rightRelativeKFlat R G F S)
local notation "QP" => BimoduleTensor.compose R F E D Q P
local notation "SQ" => BimoduleTensor.compose R G F E S Q
local notation "hQP" => Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP
local notation "hSQ" => Bimodule.rightRelativeKFlat_compose R G F E S Q hS hQ
local notation "Hₗ" => BimoduleTensor.compose R G F D S QP
local notation "Hᵣ" => BimoduleTensor.compose R G E D SQ P
local notation "hHₗ" => Bimodule.rightRelativeKFlat_compose R G F D S QP hS hQP
local notation "hHᵣ" => Bimodule.rightRelativeKFlat_compose R G E D SQ P hSQ hP
local notation "L₀" => dgRelativeKFlatResolution R D
local notation "L₁" => dgRelativeKFlatResolution R E
local notation "L₂" => dgRelativeKFlatResolution R F
local notation "L₃" => dgRelativeKFlatResolution R G
local notation "F₀" => dgKernelDerivedInfinity R D E P
local notation "F₁" => dgKernelDerivedInfinity R E F Q
local notation "F₂" => dgKernelDerivedInfinity R F G S
local notation "G₀" => dgRelativeKFlatKernelNerve R D E P hP
local notation "G₁" => dgRelativeKFlatKernelNerve R E F Q hQ
local notation "G₂" => dgRelativeKFlatKernelNerve R F G S hS
local notation "F₀₂" => dgKernelDerivedInfinity R D F QP
local notation "F₁₃" => dgKernelDerivedInfinity R E G SQ
local notation "G₀₂" => dgRelativeKFlatKernelNerve R D F QP hQP
local notation "G₁₃" => dgRelativeKFlatKernelNerve R E G SQ hSQ
local notation "Tₗ" => dgKernelDerivedInfinity R D G Hₗ
local notation "Tᵣ" => dgKernelDerivedInfinity R D G Hᵣ
local notation "Nₗ" => dgRelativeKFlatKernelNerve R D G Hₗ hHₗ
local notation "Nᵣ" => dgRelativeKFlatKernelNerve R D G Hᵣ hHᵣ
local notation "x₀" => dgRelativeKFlatKernelNerve_derivedIso R D E P hP
local notation "x₁" => dgRelativeKFlatKernelNerve_derivedIso R E F Q hQ
local notation "x₂" => dgRelativeKFlatKernelNerve_derivedIso R F G S hS
local notation "x₀₂" => dgRelativeKFlatKernelNerve_derivedIso R D F QP hQP
local notation "x₁₃" => dgRelativeKFlatKernelNerve_derivedIso R E G SQ hSQ
local notation "xₗ" => dgRelativeKFlatKernelNerve_derivedIso R D G Hₗ hHₗ
local notation "xᵣ" => dgRelativeKFlatKernelNerve_derivedIso R D G Hᵣ hHᵣ
local notation "k₀" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P Q hP
local notation "k₁" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R E F G Q S hQ
local notation "kₗ" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D F G QP S hQP
local notation "kᵣ" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E G P SQ hP
local notation "a₀" => dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ
local notation "a₁" => dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS
local notation "aₗ" => dgRelativeKFlatKernelCompositionIso R D F G QP S hQP hS
local notation "aᵣ" => dgRelativeKFlatKernelCompositionIso R D E G P SQ hP hSQ
local notation "e" => dgKernelDerivedInfinity_bimoduleIso R D G
  (BimoduleTensor.associatorIso R G F E D S Q P)
local notation "e₀" => dgRelativeKFlatKernelBimoduleIso R D G
  (BimoduleTensor.associatorIso R G F E D S Q P) hHᵣ hHₗ
include hS in
/-- 元の指定導来合成子の五角式は、指定 K-flat 分解の前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_pentagon_precomp :
    FunctorIso.precomp (FunctorIso.postcomp k₀ F₂ ≪≫ kₗ) L₀ =
      FunctorIso.precomp (FunctorIso.precomp k₁ F₀ ≪≫ kᵣ ≪≫ e) L₀ := by
  have hl := comparisonComposition_left_path L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂
    F₀₂ Tₗ G₀₂ Nₗ x₀ x₁ x₂ x₀₂ xₗ k₀ kₗ a₀ aₗ
    (compositor_comparison R D E F P Q hP hQ)
    (compositor_comparison R D F G QP S hQP hS)
  have hr := comparisonComposition_right_path L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂
    F₁₃ Tᵣ G₁₃ Nᵣ x₀ x₁ x₂ x₁₃ xᵣ k₁ kᵣ a₁ aᵣ
    (compositor_comparison R E F G Q S hQ hS)
    (compositor_comparison R D E G P SQ hP hSQ)
  have hn := comparisonCompositionIso_assoc L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂ x₀ x₁ x₂
  have ht := dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D G
    (BimoduleTensor.associatorIso R G F E D S Q P) hHᵣ hHₗ
  have hp : FunctorIso.postcomp a₀ G₂ ≪≫ aₗ = (FunctorIso.precomp a₁ G₀ ≪≫ aᵣ) ≪≫ e₀ := by
    simpa only [Iso.trans_assoc] using!
      dgRelativeKFlatKernelCompositionIso_pentagon R D E F G P Q S hP hQ hS
  have h := pentagonComparison_transfer L₀ L₃ ((F₀ ≫ F₁) ≫ F₂) Tₗ Tᵣ
    ((G₀ ≫ G₁) ≫ G₂) Nₗ Nᵣ xₗ xᵣ _ _ (FunctorIso.postcomp k₀ F₂ ≪≫ kₗ)
    (FunctorIso.precomp k₁ F₀ ≪≫ kᵣ) (FunctorIso.postcomp a₀ G₂ ≪≫ aₗ)
    (FunctorIso.precomp a₁ G₀ ≪≫ aᵣ) e e₀
    hl hr hn ht hp
  simpa only [Iso.trans_assoc] using! h
include hS in
/-- 元の指定導来合成子は、同じ双加群結合子の作用と五角経路を満たす。 -/
lemma dgKernelDerivedInfinity_compIso_pentagon :
    FunctorIso.postcomp k₀ F₂ ≪≫ kₗ = FunctorIso.precomp k₁ F₀ ≪≫ kᵣ ≪≫ e := by
  exact functorIso_precomp_eq_of_isFullyFaithful L₀
    (dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (dgModuleDerivedInfinityCategory R G)) _ _
    (dgKernelDerivedInfinity_compIso_pentagon_precomp R D E F G P Q S hP hQ hS)
end
end SerrePositivity.InfinityCategories
