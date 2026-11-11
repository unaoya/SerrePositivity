module

public import SerrePositivity.KST.NonConnective.SequentialRawHomDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration

/-!
概要：BF 置換への全パラメータの持ち上げを反変 Hom の end 全体で選ぶ。
方針：係数ごとの自明 Kan fibration を Bousfield–Kan end へ移し、厳密な右切断を取る。
規約：元の段ごとの余極限注入の図式を射影で厳密に回収する。
使われ方：K-7 の実 Sp 余錐の高次整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 反転した全 Hom の係数図式。 -/
abbrev sequentialReflectedRawHomDiagram (D : SpectrumSequence.{u}) (Z : KanSequence.{u}) :=
  sequentialRawHomDiagram D Z ⋙ SSet.opFunctor

/-- BF 置換の射影が全反転 Hom 図式へ誘導する自然変換。 -/
def sequentialReflectedProjection (D : SpectrumSequence.{u}) :
    sequentialReflectedRawHomDiagram D (sequentialSpectrum D).toKanSequence ⟶
      sequentialReflectedRawHomDiagram D (OmegaSpectrum.filteredKanSequence D) :=
  Functor.whiskerRight
    (sequentialRawHomPost D (OmegaSpectrum.filteredSequenceComparison D)) SSet.opFunctor

/-- 元の BF 射影の全反転 Hom 成分は自明 Kan fibration。 -/
instance sequentialReflectedProjection_trivial (D : SpectrumSequence.{u})
    (i : SequentialIndex.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((sequentialReflectedProjection D).app i) := by
  let p := OmegaSpectrum.filteredSequenceComparison D
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((sequentialRawHomPost D p).app i) :=
    sequentialRawHomPost_trivial D p
      (fun k ↦ (KanSequence.replacementStage
        (OmegaSpectrum.filteredKanSequence D) k).projection_rlp) i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalTrivialKanFibration_op ((sequentialRawHomPost D p).app i)

/-- BF 射影が誘導する、反転 Hom の end 全体の自明 Kan fibration。 -/
instance sequentialReflectedEndProjection_trivial (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
      (sequentialReflectedProjection D)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_trivialKanFibration (sequentialReflectedProjection D)

/-- 全反転 Hom end の同じ射影に対する、実右切断とその厳密な比較式。 -/
def sequentialReflectedEndSectionData (D : SpectrumSequence.{u}) :
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
        (sequentialReflectedRawHomDiagram D (OmegaSpectrum.filteredKanSequence D)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (sequentialReflectedRawHomDiagram D (sequentialSpectrum D).toKanSequence) //
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
        (sequentialReflectedProjection D) = 𝟙 _} := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
    (sequentialReflectedProjection D)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) (initial.to (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
    (sequentialReflectedRawHomDiagram D (OmegaSpectrum.filteredKanSequence D)))) inferInstance
  let sq : CommSq (initial.to (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
    (sequentialReflectedRawHomDiagram D (sequentialSpectrum D).toKanSequence)))
    (initial.to (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
    (sequentialReflectedRawHomDiagram D (OmegaSpectrum.filteredKanSequence D)))) q (𝟙 _) :=
    ⟨by apply initial.hom_ext⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 段ごとの注入の厳密錐を反転した end の標準点。 -/
def sequentialReflectedRawInjectionPoint (D : SpectrumSequence.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (sequentialReflectedRawHomDiagram D (OmegaSpectrum.filteredKanSequence D))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone (sequentialRawInjectionCone D))).app _
    (SSet.opObjEquiv.symm (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))

/-- 元の BF 候補への、全ての高次整合を同時に持ち上げた end の点。 -/
def sequentialReflectedBFInjectionPoint (D : SpectrumSequence.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (sequentialReflectedRawHomDiagram D (sequentialSpectrum D).toKanSequence)) _⦋0⦌ :=
  (sequentialReflectedEndSectionData D).val.app _ (sequentialReflectedRawInjectionPoint D)

/-- 持ち上げた全 end の点を射影すると、元の注入の点そのものに戻る。 -/
lemma sequentialReflectedBFInjectionPoint_projection (D : SpectrumSequence.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
      (sequentialReflectedProjection D)).app _ (sequentialReflectedBFInjectionPoint D) =
        sequentialReflectedRawInjectionPoint D := by
  change ((sequentialReflectedEndSectionData D).val ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
      (sequentialReflectedProjection D)).app _ (sequentialReflectedRawInjectionPoint D) = _
  rw [(sequentialReflectedEndSectionData D).property]
  rfl

end SerrePositivity.KST.NonConnective
