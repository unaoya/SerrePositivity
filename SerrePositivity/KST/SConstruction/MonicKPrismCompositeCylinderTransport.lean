module
public import SerrePositivity.KST.SConstruction.MonicKPrismProjectedSecondTrace
public import SerrePositivity.KST.SConstruction.SuspendedFamilyMiddleTransfer
public import SerrePositivity.KST.SConstruction.FamilyInterchangeCylinderChains

/-! # 後続適合円柱を元の段族から補正済み段族へ運ぶ
概要：元の後続適合円柱の合成を、前の全補正区間に沿って二次元補正列で移す。
方針：同じ交換正方形を円柱間のホモトピーとして使い、元の射影を中間で交換する。
規約：元の全時刻・同じ BF 族と置換射影を保持する。
使われ方：後半射影に現れる適合区間と前半の交換正方形列の終端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance compositeCylinderTransportPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 前の指定段族を suspension し、元の後続適合円柱と合成する全円柱。 -/
def monicKPrismCompositeCompatibilityAt (n : ℕ)
    (v : nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶ (PointedObject.basedHom
      ((kOmegaSpectrum (F.obj x)).level n).space ((kKanSequence (F.obj y)).level n).space).right) :=
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  lift (fst (P ⊗ Q) Δ[1] ≫ fst P Q ≫ v ≫
      (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj y)).level n).space).right)
    (monicKPrismCompositeCompatibility F f g n).h ≫
      eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj y)).level n).space)
        ((kKanSequence (F.obj z)).level (n + 1)).space

/-- 元の後続適合円柱を前の元の段から補正済み段へ運ぶ、実二次元補正有限列。 -/
def monicKPrismCompositeCompatibilityTransportChain (n : ℕ) :
    FamilyHomotopyChain
      (monicKPrismCompositeCompatibilityAt F f g n (monicKPrismRawLevelFamily n F f))
      (monicKPrismCompositeCompatibilityAt F f g n (monicKPrismTracedStage F f n).val) := by
  let c := familyHomotopyChainMap
    (familyHomotopyChainPrecomp
      (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)))
      (monicKPrismTracedStage F f n).chain)
    (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
      ((kKanSequence (F.obj y)).level n).space).right
  let d := familyInterchangeCylinderChain c (monicKPrismCompositeCompatibility F f g n).h
    (eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj y)).level n).space)
      ((kKanSequence (F.obj z)).level (n + 1)).space)
  exact familyHomotopyChainSourceTransport
    (familyHomotopyChainTargetTransport d (by
      simp only [monicKPrismCompositeCompatibilityAt, Category.assoc]))
    (by simp only [monicKPrismCompositeCompatibilityAt, Category.assoc])

/-- 後半射影の先頭は、前の補正済み段と元の同じ後続適合円柱の実合成である。 -/
lemma monicKPrismCompositeSecondCompatibility_at_stage (n : ℕ) :
    monicKPrismCompositeSecondCompatibility F f g n =
      monicKPrismCompositeCompatibilityAt F f g n (monicKPrismTracedStage F f n).val := by
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  let v := fst (P ⊗ Q) (Δ[1] : SSet.{u}) ≫ fst P Q ≫ monicKPrismTracedBFFamily F f ≫
    OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n
  have hp : v ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
      ((monicKKanSequenceProjection (F.obj y)).app n)).right =
      fst (P ⊗ Q) Δ[1] ≫ fst P Q ≫ (monicKPrismTracedStage F f n).val := by
    dsimp only [v]
    simpa only [Category.assoc, monicKPrismTracedStage] using congrArg
      (fun h => (fst (P ⊗ Q) (Δ[1] : SSet.{u}) ≫ fst P Q) ≫ h)
      (monicKPrismTracedBFFamily_evaluation F f n)
  rw [monicKPrismCompositeSecondCompatibility, spectrumSuspendedCylinderComposite,
    monicKPrismRawSequenceCompatibility_h, monicKPrismSpecifiedCompatibilityFamily_h]
  change lift (v ≫ (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
      ((kOmegaSpectrum (F.obj y)).level n).space).right)
      ((monicKPrismCompositeCompatibility F f g n).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁
          (monicKKanSequenceProjection (F.obj y)).app n)
          ((kKanSequence (F.obj z)).level (n + 1)).space) ≫ _ = _
  rw [pointed_suspension_middle_lift]
  change lift ((v ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
      ((monicKKanSequenceProjection (F.obj y)).app n)).right) ≫
      (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj y)).level n).space).right) _ ≫ _ = _
  rw [hp]
  rfl

/-- 二次元補正列の終点を、後半射影に現れる同じ実適合区間として保存する。 -/
def monicKPrismCompositeSecondCompatibilityTransport (n : ℕ) :
    FamilyHomotopyChain
      (monicKPrismCompositeCompatibilityAt F f g n (monicKPrismRawLevelFamily n F f))
      (monicKPrismCompositeSecondCompatibility F f g n) :=
  familyHomotopyChainTargetTransport (monicKPrismCompositeCompatibilityTransportChain F f g n)
    (monicKPrismCompositeSecondCompatibility_at_stage F f g n).symm

/-- 二次元補正列の全区間は、元の同じ適合円柱と補正全区間の交換正方形である。 -/
lemma monicKPrismCompositeSecondCompatibilityTransport_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismCompositeSecondCompatibilityTransport F f g n) =
      (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map (fun h =>
        familyInterchangeSquare (monicKPrismCompositeCompatibility F f g n).h
          ((fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
            (Δ[1] : SSet.{u})) ≫ h ≫
            (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
              ((kKanSequence (F.obj y)).level n).space).right)
          ((β_ _ _).hom ≫
            eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
              (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj y)).level n).space)
              ((kKanSequence (F.obj z)).level (n + 1)).space)) := by
  simp only [monicKPrismCompositeSecondCompatibilityTransport,
    monicKPrismCompositeCompatibilityTransportChain, familyHomotopyChainTargetTransport_trace,
    familyHomotopyChainSourceTransport_trace, familyInterchangeCylinderChain_trace,
    familyHomotopyChainMap_trace, familyHomotopyChainPrecomp_trace,
    List.map_map, Function.comp_def, Category.assoc]

/-- 前半補正の射影に現れる元の前の適合円柱の実後合成。 -/
def monicKPrismCompositeFirstCompatibility (n : ℕ) :=
  (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
    (Δ[1] : SSet.{u})) ≫ (monicKPrismRawSequenceCompatibility n F f).h ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
        (kKanSequenceLevelMap (F.map g) (n + 1))).right

/-- 合成補正全体の射影を、元の適合区間・交換面・後続適合区間・前段の後半へ分解する。 -/
lemma monicKPrismTracedCompositeCorrectionChain_projection_trace (n : ℕ) :
    (familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g (n + 1))).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      monicKPrismCompositeFirstCompatibility F f g n ::
        ((monicKPrismCompatibilityInterchangeSquares F f g n).map (SSet.ι₀ ≫ ·) ++
          monicKPrismCompositeSecondCompatibility F f g n ::
            (monicKPrismCompositeSecondTrace F f g n).map
              (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x))
                (kKanSequence (F.obj z)) n)) := by
  rw [monicKPrismTracedCompositeCorrectionChain_trace, List.map_append,
    monicKPrismCompositeFirstTrace_projection_squares, monicKPrismCompositeSecondTrace_projection,
    List.cons_append]
  rfl

/-- 零段の二次元補正列にも区間はなく、元の同じ適合円柱を変更しない。 -/
lemma monicKPrismCompositeSecondCompatibilityTransport_zero_trace :
    familyHomotopyChainTrace (monicKPrismCompositeSecondCompatibilityTransport F f g 0) = [] := by
  rw [monicKPrismCompositeSecondCompatibilityTransport_trace]
  rfl

/-- 零段では後半の適合円柱は、元の段族を使う円柱と厳密に同じである。 -/
lemma monicKPrismCompositeSecondCompatibility_zero :
    monicKPrismCompositeSecondCompatibility F f g 0 =
      monicKPrismCompositeCompatibilityAt F f g 0 (monicKPrismRawLevelFamily 0 F f) :=
  (familyHomotopyChain_eq_of_trace_nil (monicKPrismCompositeSecondCompatibilityTransport F f g 0)
    (monicKPrismCompositeSecondCompatibilityTransport_zero_trace F f g)).symm

end SerrePositivity.KST.SConstruction
