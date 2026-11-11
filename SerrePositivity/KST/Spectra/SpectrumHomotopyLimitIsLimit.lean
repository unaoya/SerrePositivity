module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitConeSourceRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConeSourceApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy

/-!
概要：任意の小さい通常の BF 図式の元の homotopy limit は、実際の coherent な極限錐の頂点。
方針：錐全体の全 Hom 比較族の頂点評価と制限を照合し、γ3 の native な極限判定を適用する。
規約：元の BF 模型・元の図式・元の比較を保持する。任意の coherent 図式への拡張は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance homotopyLimitIsLimitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyLimitIsLimitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]

/-- 元の BF homotopy limit を頂点とする構成済みの coherent 錐は、実際の ∞ 極限錐。 -/
lemma homotopyLimitCoherentCone_isLimit (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (homotopyLimitCoherentCone D) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCone_isLimit_of_family_lifts (homotopyLimitCoherentCone D)
    (homotopyLimit D) (homotopyLimitCoherentCone_vertex D)
    (fun X ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (homotopyLimitCoherentCone D)
      (homotopyLimit D) (homotopyLimitCoherentCone_vertex D) X)
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_evaluation _ _ _ _
  · intro X
    rw [homotopyLimitCoherentConeSourceFamily_restrict]
    exact homotopyLimitNativeConeComparison_homotopyEquivalence D X

/-- 任意の小さい通常の BF 図式の coherent nerve は、実際の Sp 内に極限を持つ。 -/
lemma strictCoherentDiagram_hasLimit (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) :=
  ⟨homotopyLimitCoherentCone D, homotopyLimitCoherentCone_isLimit D⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
