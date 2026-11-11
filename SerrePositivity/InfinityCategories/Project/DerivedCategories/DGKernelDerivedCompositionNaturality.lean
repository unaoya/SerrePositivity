module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionCompositorNaturalityTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositorCoherence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
private lemma compositor_comparison (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P Q hP).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F (BimoduleTensor.compose R F E D Q P)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q hQ) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_assoc] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositor_iso R D E F P Q hP hQ
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
variable (f : P ≅ P') (g : Q ≅ Q')
  (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
  (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'))
  (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))
  (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'))
local notation "C₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q₀ P₀
local notation "C₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q₁ P₁
local notation "hC₀" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP
local notation "hC₁" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'
local notation "L₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D
local notation "L₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E
local notation "L₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F
local notation "F₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P₀
local notation "F₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P₁
local notation "H₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q₀
local notation "H₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q₁
local notation "G₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₀ hP
local notation "G₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP'
local notation "K₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ
local notation "K₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₁ hQ'
local notation "T₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D F C₀
local notation "T₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D F C₁
local notation "U₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F C₀ hC₀
local notation "U₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F C₁ hC₁
local notation "xP₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P₀ hP
local notation "xP₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P₁ hP'
local notation "xQ₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q₀ hQ
local notation "xQ₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q₁ hQ'
local notation "xC₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F C₀ hC₀
local notation "xC₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F C₁ hC₁
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R E F g
local notation "e₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E f hP hP'
local notation "d₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R E F g hQ hQ'
local notation "c" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleComposeIso R D E F f g
local notation "t" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D F c
local notation "u" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D F c hC₀ hC₁
local notation "k₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₀ Q₀ hP
local notation "k₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₁ Q₁ hP'
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ
local notation "a₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ'
include hP hP' hQ hQ' in
/-- 元の指定導来合成子の自然性は、指定分解の全前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_naturality_precomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (k₀ ≪≫ t) L₀ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e H₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d F₁ ≪≫ k₁) L₀ := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso_naturality L₀ L₁ L₂ F₀ F₁ H₀ H₁ G₀ G₁ K₀ K₁
    xP₀ xP₁ xQ₀ xQ₁ e e₀ d d₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D E f hP hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R E F g hQ hQ')
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D F c hC₀ hC₁
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_naturality R D E F f g hP hP' hQ hQ'
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.compositionComparison_transfer_naturality L₀ L₂
    (F₀ ≫ H₀) (F₁ ≫ H₁) T₀ T₁ (G₀ ≫ K₀) (G₁ ≫ K₁) U₀ U₁ xC₀ xC₁ _ _ k₀ k₁
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e H₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d F₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e₀ K₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d₀ G₁) t u a₀ a₁
    (compositor_comparison R D E F P₀ Q₀ hP hQ)
    (compositor_comparison R D E F P₁ Q₁ hP' hQ') hn hx
    (by simpa only [Iso.trans_assoc] using! ha)
  simpa only [Iso.trans_assoc] using! h
include hP hP' hQ hQ' in
/-- 元の指定導来合成子 κ は、同じ二つの双加群同型の作用に自然。 -/
lemma dgKernelDerivedInfinity_compIso_naturality :
    k₀ ≪≫ t = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e H₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp d F₁ ≪≫ k₁ := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_eq_of_isFullyFaithful L₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R F)) _ _
    (dgKernelDerivedInfinity_compIso_naturality_precomp R D E F f g hP hP' hQ hQ')
end SerrePositivity.InfinityCategories.Project.DerivedCategories
