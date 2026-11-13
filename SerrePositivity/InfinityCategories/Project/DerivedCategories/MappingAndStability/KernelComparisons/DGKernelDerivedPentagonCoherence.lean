module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionComparisonLeftPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionComparisonRightPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionPentagonTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGRelativeKFlatComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGRelativeKFlatCompositorCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGRelativeKFlatCompositionPentagon
/-!
概要：元の指定導来 kernel 合成子 κ の五角式を証明する。
方針：左右経路を同じ水平三重比較へ移し、同じ終辺の ξ 自然性と全前合成で反映する。
規約：三 kernel の右相対 K-flat 性を明示し、原 Hom の平坦性を追加しない。
使われ方：元の指定導来 kernel の coherence と一般 cell 模型への移送。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G] [Small.{u} G]
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
variable (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F)
  (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q)
  (hS : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R G F S)
local notation "QP" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q P
local notation "SQ" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E S Q
local notation "hQP" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP
local notation "hSQ" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R G F E S Q hS hQ
local notation "Hₗ" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F D S QP
local notation "Hᵣ" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G E D SQ P
local notation "hHₗ" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R G F D S QP hS hQP
local notation "hHᵣ" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R G E D SQ P hSQ hP
local notation "L₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D
local notation "L₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E
local notation "L₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F
local notation "L₃" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R G
local notation "F₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P
local notation "F₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q
local notation "F₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R F G S
local notation "G₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP
local notation "G₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ
local notation "G₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R F G S hS
local notation "F₀₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D F QP
local notation "F₁₃" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E G SQ
local notation "G₀₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F QP hQP
local notation "G₁₃" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E G SQ hSQ
local notation "Tₗ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D G Hₗ
local notation "Tᵣ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D G Hᵣ
local notation "Nₗ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D G Hₗ hHₗ
local notation "Nᵣ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D G Hᵣ hHᵣ
local notation "x₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP
local notation "x₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q hQ
local notation "x₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R F G S hS
local notation "x₀₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F QP hQP
local notation "x₁₃" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E G SQ hSQ
local notation "xₗ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D G Hₗ hHₗ
local notation "xᵣ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D G Hᵣ hHᵣ
local notation "k₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P Q hP
local notation "k₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R E F G Q S hQ
local notation "kₗ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D F G QP S hQP
local notation "kᵣ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E G P SQ hP
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ
local notation "a₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R E F G Q S hQ hS
local notation "aₗ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D F G QP S hQP hS
local notation "aᵣ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E G P SQ hP hSQ
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D G
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P)
local notation "e₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D G
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P) hHᵣ hHₗ
include hS in
/-- 元の指定導来合成子の五角式は、指定 K-flat 分解の前合成後に成立。 -/
lemma dgKernelDerivedInfinity_compIso_pentagon_precomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp k₀ F₂ ≪≫ kₗ) L₀ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp k₁ F₀ ≪≫ kᵣ ≪≫ e) L₀ := by
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonComposition_left_path L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂
    F₀₂ Tₗ G₀₂ Nₗ x₀ x₁ x₂ x₀₂ xₗ k₀ kₗ a₀ aₗ
    (compositor_comparison R D E F P Q hP hQ)
    (compositor_comparison R D F G QP S hQP hS)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonComposition_right_path L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂
    F₁₃ Tᵣ G₁₃ Nᵣ x₀ x₁ x₂ x₁₃ xᵣ k₁ kᵣ a₁ aᵣ
    (compositor_comparison R E F G Q S hQ hS)
    (compositor_comparison R D E G P SQ hP hSQ)
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso_assoc L₀ L₁ L₂ L₃ F₀ F₁ F₂ G₀ G₁ G₂ x₀ x₁ x₂
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality R D G
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E D S Q P) hHᵣ hHₗ
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a₀ G₂ ≪≫ aₗ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a₁ G₀ ≪≫ aᵣ) ≪≫ e₀ := by
    simpa only [Iso.trans_assoc] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_pentagon R D E F G P Q S hP hQ hS
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pentagonComparison_transfer L₀ L₃ ((F₀ ≫ F₁) ≫ F₂) Tₗ Tᵣ
    ((G₀ ≫ G₁) ≫ G₂) Nₗ Nᵣ xₗ xᵣ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp k₀ F₂ ≪≫ kₗ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp k₁ F₀ ≪≫ kᵣ) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a₀ G₂ ≪≫ aₗ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp a₁ G₀ ≪≫ aᵣ) e e₀
    hl hr hn ht hp
  simpa only [Iso.trans_assoc] using! h
include hS in
/-- 元の指定導来合成子は、同じ双加群結合子の作用と五角経路を満たす。 -/
lemma dgKernelDerivedInfinity_compIso_pentagon :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp k₀ F₂ ≪≫ kₗ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp k₁ F₀ ≪≫ kᵣ ≪≫ e := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_eq_of_isFullyFaithful L₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R G)) _ _
    (dgKernelDerivedInfinity_compIso_pentagon_precomp R D E F G P Q S hP hQ hS)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
