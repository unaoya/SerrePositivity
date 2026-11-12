module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKConeSourceRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConeSourceApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy

/-!
概要：元の円評価の BK 切断点が与える cotensor 錐は、実際の Sp の ∞ 極限錐。
方針：錐全体の全 Hom 族の頂点評価と制限を照合し、共有 γ3 の native な判定へ渡す。
規約：既存の別の円評価四角形との比較は後続。頂点の同型だけから極限性を主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleBKIsLimitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleBKIsLimitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の円 cotensor の恒等射の BK 切断点から作った錐は、実際の Sp の極限錐。 -/
lemma circleBKCoherentCone_isLimit (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (circleBKCoherentCone Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCone_isLimit_of_family_lifts (circleBKCoherentCone Y)
    (cotensor PointedSimplicialSet.circle Y) (circleBKCoherentCone_vertex Y)
    (fun X ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (circleBKCoherentCone Y)
      (cotensor PointedSimplicialSet.circle Y) (circleBKCoherentCone_vertex Y) X)
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_evaluation _ _ _ _
  · intro X
    rw [circleBKCoherentConeSourceFamily_restrict]
    exact circleBKNativeConeComparison_homotopyEquivalence X Y

end SerrePositivity.KST.Spectra.OmegaSpectrum
