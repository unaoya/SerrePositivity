module
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.ActionCompositorNaturalityTransfer
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositorCoherence
/-!
概要：元の指定導来 kernel 合成子 κ の双加群同型への二変数自然性を証明する。
方針：同じ水平比較・指定合成子正方形・ξ 自然性を保って、全前合成から反映する。
規約：四端の kernel の右相対 K-flat 性を明示し、原 Hom の平坦性は追加しない。
使われ方：左単位三角式と一般 cell 模型への coherence の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
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
variable {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R F E}
local notation "P₀" => BimoduleCategory.underlying R E D P
local notation "P₁" => BimoduleCategory.underlying R E D P'
local notation "Q₀" => BimoduleCategory.underlying R F E Q
local notation "Q₁" => BimoduleCategory.underlying R F E Q'
variable (f : P ≅ P') (g : Q ≅ Q')
  (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
  (hP' : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P'))
  (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
  (hQ' : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q'))
local notation "C₀" => BimoduleTensor.compose R F E D Q₀ P₀
local notation "C₁" => BimoduleTensor.compose R F E D Q₁ P₁
local notation "hC₀" => Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP
local notation "hC₁" => Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'
local notation "L₀" => dgRelativeKFlatResolution R D
local notation "L₁" => dgRelativeKFlatResolution R E
local notation "L₂" => dgRelativeKFlatResolution R F
local notation "F₀" => dgKernelDerivedInfinity R D E P₀
local notation "F₁" => dgKernelDerivedInfinity R D E P₁
local notation "H₀" => dgKernelDerivedInfinity R E F Q₀
local notation "H₁" => dgKernelDerivedInfinity R E F Q₁
local notation "G₀" => dgRelativeKFlatKernelNerve R D E P₀ hP
local notation "G₁" => dgRelativeKFlatKernelNerve R D E P₁ hP'
local notation "K₀" => dgRelativeKFlatKernelNerve R E F Q₀ hQ
local notation "K₁" => dgRelativeKFlatKernelNerve R E F Q₁ hQ'
local notation "T₀" => dgKernelDerivedInfinity R D F C₀
local notation "T₁" => dgKernelDerivedInfinity R D F C₁
local notation "U₀" => dgRelativeKFlatKernelNerve R D F C₀ hC₀
local notation "U₁" => dgRelativeKFlatKernelNerve R D F C₁ hC₁
local notation "xP₀" => dgRelativeKFlatKernelNerve_derivedIso R D E P₀ hP
local notation "xP₁" => dgRelativeKFlatKernelNerve_derivedIso R D E P₁ hP'
local notation "xQ₀" => dgRelativeKFlatKernelNerve_derivedIso R E F Q₀ hQ
local notation "xQ₁" => dgRelativeKFlatKernelNerve_derivedIso R E F Q₁ hQ'
local notation "xC₀" => dgRelativeKFlatKernelNerve_derivedIso R D F C₀ hC₀
local notation "xC₁" => dgRelativeKFlatKernelNerve_derivedIso R D F C₁ hC₁
local notation "e" => dgKernelDerivedInfinity_bimoduleIso R D E f
local notation "d" => dgKernelDerivedInfinity_bimoduleIso R E F g
local notation "e₀" => dgRelativeKFlatKernelBimoduleIso R D E f hP hP'
local notation "d₀" => dgRelativeKFlatKernelBimoduleIso R E F g hQ hQ'
local notation "c" => dgKernelBimoduleComposeIso R D E F f g
local notation "t" => dgKernelDerivedInfinity_bimoduleIso R D F c
local notation "u" => dgRelativeKFlatKernelBimoduleIso R D F c hC₀ hC₁
local notation "k₀" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₀ Q₀ hP
local notation "k₁" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₁ Q₁ hP'
local notation "a₀" => dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ
local notation "a₁" => dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ'
include hP hP' hQ hQ' in
/-- 元の指定導来合成子の自然性は、指定分解の全前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_naturality_precomp :
    FunctorIso.precomp (k₀ ≪≫ t) L₀ =
    FunctorIso.precomp (FunctorIso.postcomp e H₀ ≪≫ FunctorIso.precomp d F₁ ≪≫ k₁) L₀ := by
  have hn := comparisonCompositionIso_naturality L₀ L₁ L₂ F₀ F₁ H₀ H₁ G₀ G₁ K₀ K₁
    xP₀ xP₁ xQ₀ xQ₁ e e₀ d d₀
    (dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D E f hP hP')
    (dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R E F g hQ hQ')
  have hx := dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D F c hC₀ hC₁
  have ha := dgRelativeKFlatKernelCompositionIso_naturality R D E F f g hP hP' hQ hQ'
  have h := compositionComparison_transfer_naturality L₀ L₂
    (F₀ ≫ H₀) (F₁ ≫ H₁) T₀ T₁ (G₀ ≫ K₀) (G₁ ≫ K₁) U₀ U₁ xC₀ xC₁ _ _ k₀ k₁
    (FunctorIso.postcomp e H₀ ≪≫ FunctorIso.precomp d F₁)
    (FunctorIso.postcomp e₀ K₀ ≪≫ FunctorIso.precomp d₀ G₁) t u a₀ a₁
    (compositor_comparison R D E F P₀ Q₀ hP hQ)
    (compositor_comparison R D E F P₁ Q₁ hP' hQ') hn hx
    (by simpa only [Iso.trans_assoc] using! ha)
  simpa only [Iso.trans_assoc] using! h
include hP hP' hQ hQ' in
/-- 元の指定導来合成子 κ は、同じ二つの双加群同型の作用に自然。 -/
lemma dgKernelDerivedInfinity_compIso_naturality :
    k₀ ≪≫ t = FunctorIso.postcomp e H₀ ≪≫ FunctorIso.precomp d F₁ ≪≫ k₁ := by
  exact functorIso_precomp_eq_of_isFullyFaithful L₀
    (dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (dgModuleDerivedInfinityCategory R F)) _ _
    (dgKernelDerivedInfinity_compIso_naturality_precomp R D E F f g hP hP' hQ hQ')
end SerrePositivity.InfinityCategories
