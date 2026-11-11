module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitIsLimit
public import SerrePositivity.KST.Spectra.FixedPointSpectra

/-!
概要：元の hG と homotopy Tot は、元の作用図式・余単体図式の Sp 内の ∞ 極限。
方針：任意の小さい通常図式の coherent 極限錐を、既存の二つの添字図式へ適用する。
規約：元の BF 対象を頂点に持つ実際の極限錐を公開する。群の有限性・Reedy 条件は不要。
使われ方：局所化不変量の値域としての Sp と、既存の整数次数の界面の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
local instance fixedPointInfinitySimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の群作用図式上の、元の hG を頂点とする coherent な錐。 -/
def homotopyFixedPointsInfinityCone {G : Type u} [Group G] (A : GroupAction.{u} G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A)) :=
  OmegaSpectrum.homotopyLimitCoherentCone _

/-- hG の錐の頂点は、元の BF hG 対象そのもの。 -/
lemma homotopyFixedPointsInfinityCone_vertex {G : Type u} [Group G] (A : GroupAction.{u} G) :
    (homotopyFixedPointsInfinityCone A).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFixedPoints A) :=
  OmegaSpectrum.homotopyLimitCoherentCone_vertex _

/-- 元の hG 対象の coherent な錐は、Sp 内の実際の ∞ 極限錐。 -/
lemma homotopyFixedPointsInfinityCone_isLimit {G : Type u} [Group G] (A : GroupAction.{u} G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (homotopyFixedPointsInfinityCone A) :=
  OmegaSpectrum.homotopyLimitCoherentCone_isLimit _

/-- 元の余単体図式上の、元の homotopy Tot を頂点とする coherent な錐。 -/
def homotopyTotalizationInfinityCone (D : CosimplicialObject OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ D)) :=
  OmegaSpectrum.homotopyLimitCoherentCone _

/-- Tot の錐の頂点は、元の BF homotopy Tot 対象そのもの。 -/
lemma homotopyTotalizationInfinityCone_vertex (D : CosimplicialObject OmegaSpectrum.{u}) :
    (homotopyTotalizationInfinityCone D).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyTotalization D) :=
  OmegaSpectrum.homotopyLimitCoherentCone_vertex _

/-- 元の homotopy Tot 対象の coherent な錐は、Sp 内の実際の ∞ 極限錐。 -/
lemma homotopyTotalizationInfinityCone_isLimit (D : CosimplicialObject OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (homotopyTotalizationInfinityCone D) :=
  OmegaSpectrum.homotopyLimitCoherentCone_isLimit _

end SerrePositivity.KST.Spectra
