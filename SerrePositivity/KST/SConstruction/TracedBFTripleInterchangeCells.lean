module
public import SerrePositivity.KST.SConstruction.TracedBFInterchangeInputs

/-! # 前二射 BF 比較と最終射の元の全補正の実交換セル
概要：元の BF 段辺と最終射の全補正を同じ二時刻で合成し、元の全交換セル列を保持する。
方針：元の単一射の全合成円柱と全 trace を、同じ豊穣合成へ渡す。
規約：全区間の順序・元の両円柱・四面・隣接面を厳密に保持する。
使われ方：正の段の左右三入力補正辺路を元の全交換面で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tripleInterchangePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance tripleInterchangeSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の BF 前二射比較辺の段評価を、後続精密化によらない同じ全円柱にする。 -/
def monicKTracedTripleBFInterchangeCylinder (n : ℕ) :=
  edgeFamilyCylinder (U := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h))
    (monicKTracedCompositionBFLevelEdge F f g n)

/-- 元の最終射の全補正円柱と前二射 BF 比較の同じ全二時刻交換面。 -/
def monicKTracedTripleInterchangeFamily (n : ℕ) :=
  pointedCorrectionInterchange (monicKPrismUnaryCorrectionData F h n).homotopy.h
    (monicKTracedTripleBFInterchangeCylinder F f g h n)

/-- 補正始点の全体と元の BF 比較円柱を同じ合成として回収する。 -/
lemma monicKTracedTripleInterchangeFamily_first_zero (n : ℕ) :
    (SSet.ι₀ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) ▷ (Δ[1] : SSet.{u})) ≫
        monicKTracedTripleInterchangeFamily F f g h n =
      lift (monicKTracedTripleBFInterchangeCylinder F f g h n)
        (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) Δ[1] ≫ monicKPrismRawLevelFamily n F h) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeFamily, pointedCorrectionInterchange_first_zero,
    (monicKPrismUnaryCorrectionData F h n).homotopy.h₀]

/-- 補正終点の全体と元の BF 比較円柱を同じ合成として回収する。 -/
lemma monicKTracedTripleInterchangeFamily_first_one (n : ℕ) :
    (SSet.ι₁ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) ▷ (Δ[1] : SSet.{u})) ≫
        monicKTracedTripleInterchangeFamily F f g h n =
      lift (monicKTracedTripleBFInterchangeCylinder F f g h n)
        (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) Δ[1] ≫ (monicKPrismTracedStage F h n).val) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeFamily, pointedCorrectionInterchange_first_one,
    (monicKPrismUnaryCorrectionData F h n).homotopy.h₁]

/-- BF 比較始点と最終射の元の全補正円柱を、同じ全側面として回収する。 -/
lemma monicKTracedTripleInterchangeFamily_second_zero (n : ℕ) :
    SSet.ι₀ ≫ monicKTracedTripleInterchangeFamily F f g h n =
      lift (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) Δ[1] ≫ SSet.ι₀ ≫
        monicKTracedTripleBFInterchangeCylinder F f g h n)
        (monicKPrismUnaryCorrectionData F h n).homotopy.h ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space :=
  pointedCorrectionInterchange_second_zero _ _

/-- BF 比較終点と最終射の元の全補正円柱も、同じ全側面として回収する。 -/
lemma monicKTracedTripleInterchangeFamily_second_one (n : ℕ) :
    SSet.ι₁ ≫ monicKTracedTripleInterchangeFamily F f g h n =
      lift (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) Δ[1] ≫ SSet.ι₁ ≫
        monicKTracedTripleBFInterchangeCylinder F f g h n)
        (monicKPrismUnaryCorrectionData F h n).homotopy.h ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space :=
  pointedCorrectionInterchange_second_one _ _

/-- 元の最終射の各全補正区間と同じ BF 比較円柱の、順序付き実交換セル列。 -/
def monicKTracedTripleInterchangeCells (n : ℕ) :=
  familyHomotopyChainInterchangeSquares (monicKPrismTracedStage F h n).chain
    (monicKTracedTripleBFInterchangeCylinder F f g h n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 元の全合成木に記録した全区間ごとに、同じ BF 円柱との交換面を一つずつ保持する。 -/
lemma monicKTracedTripleInterchangeCells_trace (n : ℕ) :
    monicKTracedTripleInterchangeCells F f g h n =
      (familyChainCompositionInputTrace (monicKPrismUnaryCorrectionData F h n).witness).map
        (fun q => pointedCorrectionInterchange q
          (monicKTracedTripleBFInterchangeCylinder F f g h n)) := by
  rw [familyChainCompositionInputTrace_eq]
  rfl

/-- 隣接する元の交換セルの共有終始面は、全実写像として厳密に一致する。 -/
lemma monicKTracedTripleInterchangeCells_glue (n : ℕ) :
    List.IsChain (fun s t =>
      (SSet.ι₁ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) ▷ (Δ[1] : SSet.{u})) ≫ s =
        (SSet.ι₀ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString h)) ▷ (Δ[1] : SSet.{u})) ≫ t)
      (monicKTracedTripleInterchangeCells F f g h n) :=
  familyHomotopyChainInterchangeSquares_glue _ _ _

/-- 零段の元の補正列は空であり、交換セルも追加しない。 -/
lemma monicKTracedTripleInterchangeCells_zero :
    monicKTracedTripleInterchangeCells F f g h 0 = [] := rfl

end SerrePositivity.KST.SConstruction
