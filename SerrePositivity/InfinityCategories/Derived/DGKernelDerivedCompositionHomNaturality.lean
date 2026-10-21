module
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonHomNaturality
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonSquareHomTransfer
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatHomComparisonNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedNaturalityTransport
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositorCoherence
/-!
概要：元の指定導来合成子 κ の任意双加群射に対する二変数自然性を証明する。
方針：元の ξ の水平二重比較と指定合成子四角形を保ち、全前合成から反映する。
規約：四端の右相対 K-flat 性を明示し、射の可逆性を要求しない。
使われ方：指定模型の変更と一般 cell 模型の coherence の移送。
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
variable (f : P ⟶ P') (g : Q ⟶ Q')
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
local notation "e" =>
  CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R D E) f
local notation "d" =>
  CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R E F) g
local notation "e₀" => dgRelativeKFlatKernelBimoduleHom R D E f hP hP'
local notation "d₀" => dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ'
local notation "c" => BimoduleTensor.composeMap R F E D g f
local notation "t" =>
  CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R D F) c
local notation "u" => dgRelativeKFlatKernelBimoduleHom R D F c hC₀ hC₁
local notation "k₀" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₀ Q₀ hP
local notation "k₁" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₁ Q₁ hP'
local notation "a₀" => dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ
local notation "a₁" => dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ'
local notation "jD" => functorHomPostcomp F₀ F₁ H₀ e ≫ functorHomPrecomp H₀ H₁ F₁ d
local notation "jK" => functorHomPostcomp G₀ G₁ K₀ e₀ ≫ functorHomPrecomp K₀ K₁ G₁ d₀
include hP hP' hQ hQ' in
lemma dgKernelDerivedInfinity_compIso_hom_naturality_precomp :
    functorHomPrecomp (F₀ ≫ H₀) T₁ L₀ ((k₀).hom ≫ t) =
      functorHomPrecomp (F₀ ≫ H₀) T₁ L₀ (jD ≫ (k₁).hom) := by
  have hn := comparisonCompositionIso_hom_naturality L₀ L₁ L₂ F₀ F₁ H₀ H₁ G₀ G₁ K₀ K₁
    xP₀ xP₁ xQ₀ xQ₁ e e₀ d d₀
    (dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R D E f hP hP')
    (dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R E F g hQ hQ')
  have hx := dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R D F c hC₀ hC₁
  have ha := dgRelativeKFlatKernelCompositionIso_naturality_hom R D E F f g hP hP' hQ hQ'
  have hat := functorHomPostcomp_iso_square a₀ a₁ jK u L₂
    (by simpa only [Category.assoc] using! ha)
  have hs := comparisonSquare_transfer_hom_naturality xC₀ xC₁
    (comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ H₀ K₀ xP₀ xQ₀)
    (comparisonCompositionIso L₀ L₁ L₂ F₁ G₁ H₁ K₁ xP₁ xQ₁)
    (FunctorIso.precomp k₀ L₀) (FunctorIso.precomp k₁ L₀)
    (functorHomPrecomp (F₀ ≫ H₀) (F₁ ≫ H₁) L₀ jD)
    (functorHomPostcomp (G₀ ≫ K₀) (G₁ ≫ K₁) L₂ jK)
    (functorHomPrecomp T₀ T₁ L₀ t) (functorHomPostcomp U₀ U₁ L₂ u)
    (FunctorIso.postcomp a₀ L₂) (FunctorIso.postcomp a₁ L₂)
    (compositor_comparison R D E F P₀ Q₀ hP hQ)
    (compositor_comparison R D E F P₁ Q₁ hP' hQ') hn hx hat
  exact functorHomPrecomp_iso_square k₀ k₁ jD t L₀ hs
include hP hP' hQ hQ' in
lemma dgKernelDerivedInfinity_compIso_hom_naturality :
    (k₀).hom ≫ t = jD ≫ (k₁).hom := by
  exact functorHomPrecomp_eq_of_isFullyFaithful L₀
    (dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (dgModuleDerivedInfinityCategory R F)) _ _
    (dgKernelDerivedInfinity_compIso_hom_naturality_precomp R D E F f g hP hP' hQ hQ')
end SerrePositivity.InfinityCategories
