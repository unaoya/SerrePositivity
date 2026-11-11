module
public import SerrePositivity.KST.SConstruction.TracedBFDirectCorrectionNormalization
public import SerrePositivity.KST.SConstruction.EdgeFamilyCylinders
public import SerrePositivity.KST.SConstruction.PointedCorrectionInterchange

/-! # 元の最終射補正と前二射 BF 比較の全段入力
概要：元の最終射の全補正と前二射の BF 比較辺を、各段の同じ実豊穣射に回収する。
方針：元の全円柱を一点で読む実辺と、元の BF 辺の同じ段評価を使う。
規約：全一単体を選び直さず、元の同じ全区間を保持する。
使われ方：三入力の合成補正の交換正方形と同じ二実三角形対の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance interchangeInputSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
/-- 先行 BF 射と後続 raw 射の同じ段における豊穣合成の実写像。 -/
def kStageRawReverseComposition (X Y Z : StableModel.{u}) (n : ℕ) :=
  pointedReverseComposition ((kOmegaSpectrum X).level n).space
    ((kOmegaSpectrum Y).level n).space ((kKanSequence Z).level n).space

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の単一射の同じ全補正円柱を、同じ直通列点の実辺として読む。 -/
def monicKTracedUnaryCorrectionPointEdge (n : ℕ) :=
  pointFamilyHomotopyEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (monicKPrismUnaryCorrectionData F f n).homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f)))

/-- 同じ実辺の全区間は、元の同じ単一射補正の直通列制限そのもの。 -/
lemma monicKTracedUnaryCorrectionPointEdge_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedUnaryCorrectionPointEdge F f n).edge =
      monicKTracedUnaryCorrectionAtPoint F f n := by
  rw [monicKTracedUnaryCorrectionPointEdge, pointFamilyHomotopyEdge_map]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, intervalParameterPoint_of_map]
  rfl

variable {z : I} (g : y ⟶ z)

/-- 元の前二射の BF 比較辺の同じ BF 段評価。標的の raw 射影は挟まない。 -/
def monicKTracedCompositionBFLevelEdge (n : ℕ) :=
  (monicKTracedSpectrumCompositionEdge F f g).map
    (OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj z)) n)

/-- 元の前二射比較辺の全一単体の段評価を厳密に回収する。 -/
lemma monicKTracedCompositionBFLevelEdge_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj z)) n :=
  (SSet.yonedaEquiv_symm_comp _ _).symm

end SerrePositivity.KST.SConstruction
