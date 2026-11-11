module
public import SerrePositivity.KST.NonConnective.DGKappaConnectedKSwindle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSplitCofiber
public import SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels

/-!
概要：D-12 正本の判定で元の分裂 cofiber 入力を供給し、同じ cone の K 消滅へ接続する。
方針：同じ五つの閉分裂関係・native 零角・零の両原始元を、D の実四角形判定へ渡す。
規約：一般 dg 加群の判定を重ねず、元のラベル作用と全二胞体を変えない。
使われ方：明示 cofiber 入力の除去と、同じ固定 dg K の連結消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance splitCofiberSupplySpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- D-12 の汎用判定は、元の各ラベルの指定二胞体の cofiber 入力を実際に供給する。 -/
theorem dgKappaSplitCofiberInput
    (X : PresentedPerfectDGObject R (DGKappaCone R D I)) : DGKappaSplitCofiberInput R D I X := by
  refine ⟨fun Z => ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSplitSquare_isPushout R (DGKappaCone R D I)
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I))
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHeadProjection R D I))
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTail R D I))
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTailProjection R D I))
    (dgKappaSplitModule_head_head R D I X) (dgKappaSplitModule_tail_tail R D I X)
    (dgKappaSplitModule_head_tail R D I X) (dgKappaSplitModule_tail_head R D I X)
    (dgKappaSplitModule_decomposition R D I X) (dgKappaSplitModuleSquareData R D I X Z)
    (dgKappaSplitModule_zero_isZeroVertex R D I X Z) rfl rfl rfl rfl rfl rfl rfl

/-- 元の点ごとの native 分裂零三角形は、追加 cofiber 仮定なしに実 cofiber 列。 -/
theorem dgKappaSplitPerfPointwiseZeroTriangle_isCofiber
    (X : PresentedPerfectDGObject R (DGKappaCone R D I)) (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (dgKappaSplitPerfPointwiseZeroTriangle R D I X Z) :=
  dgKappaSplitPerfPointwiseZeroTriangle_isCofiber_of_input R D I X
    (dgKappaSplitCofiberInput R D I X) Z

/-- D-12 の実供給後、元の同じ cone の連結 BF K の全整数群は自明。 -/
theorem dgKappaConnectedK_subsingleton_of_split (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (presentedPerfectDGStableModel R (DGKappaCone R D I))) j) :=
  dgKappaConnectedK_subsingleton R D I Z (dgKappaSplitCofiberInput R D I) j

/-- 元の同じ固定 dg K の実 BF スペクトルでも、追加 cofiber 仮定なしに全整数群が自明。 -/
theorem dgKappaFixedK_subsingleton_of_split (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgKappaConeKInput R D I)) j) :=
  dgKappaFixedK_subsingleton R D I Z (dgKappaSplitCofiberInput R D I) j

/-- 元の同じ cone の連結 BF K 頂点は、実 Sp 内の零対象。 -/
theorem dgKappaConnectedK_isZeroVertex (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (kOmegaSpectrum (presentedPerfectDGStableModel R (DGKappaCone R D I)))) :=
  Fibration.spectrum_isZeroVertex_of_homotopyGroup_subsingleton _
    (dgKappaConnectedK_subsingleton_of_split R D I Z)

/-- 元の同じ固定 dg K 入力の実スペクトル頂点も、実 Sp 内の零対象。 -/
theorem dgKappaFixedK_isZeroVertex (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaConeKInput R D I))) :=
  Fibration.spectrum_isZeroVertex_of_homotopyGroup_subsingleton _
    (dgKappaFixedK_subsingleton_of_split R D I Z)

end SerrePositivity.KST.NonConnective
