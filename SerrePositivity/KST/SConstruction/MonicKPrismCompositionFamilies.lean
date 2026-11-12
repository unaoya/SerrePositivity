module
public import SerrePositivity.KST.SConstruction.MonicKPrismTracedRectification
public import SerrePositivity.KST.SConstruction.PointedCompositeCorrectionChains
public import SerrePositivity.KST.SConstruction.KSequenceMapLaws
public import SerrePositivity.KST.Spectra.RawSpectrumMappingCompositionLaws

/-! # 二本の元の K prism の合成族と実補正列
概要：二本の補正済み K prism を合成し、その各段を元の合成射と実区間で比較する。
方針：元の単射置換の射影を挟む合成を各段で評価し、保存済みの二本の補正列を連結する。
規約：元の全精密化パラメータと全補正区間を保持する。
使われ方：入力射の合成面に指定する raw 族と、その元の段族との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
local instance prismCompositionSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の単一射の族で保存済みの、同じ補正済み段と全補正列。 -/
def monicKPrismTracedStage (n : ℕ) :=
  prescribedSequenceFamilyStage (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f) (monicKPrismTracedBoundary F f) n

/-- 元の raw 族の実評価は、保存済みの同じ補正済み段。 -/
lemma monicKPrismTracedRawFamily_evaluation (n : ℕ) :
    monicKPrismTracedRawFamily F f ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) n =
      (monicKPrismTracedStage F f n).val :=
  prescribedSequenceFamilyRectification_evaluation _ _ _ _ _ _ n

/-- 二本の全精密化族を、元の BF 写像空間で合成した族。 -/
def monicKPrismTracedCompositionFamily :=
  lift (fst _ _ ≫ monicKPrismTracedBFFamily F f)
    (snd _ _ ≫ monicKPrismTracedBFFamily F g) ≫
      OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj x))
        (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z))

/-- 二本の全精密化族を合成した、元の列への同じ raw 族。 -/
def monicKPrismTracedRawComposition :=
  lift (fst _ _ ≫ monicKPrismTracedBFFamily F f)
    (snd _ _ ≫ monicKPrismTracedRawFamily F g) ≫
      RawSpectrumMapping.composition (kOmegaSpectrum (F.obj x))
        (kOmegaSpectrum (F.obj y)) (kKanSequence (F.obj z))

/-- BF の合成族は、元の射影後に同じ raw 合成族を厳密に回収する。 -/
lemma monicKPrismTracedCompositionFamily_projection :
    monicKPrismTracedCompositionFamily F f g ≫ kRawMappingProjection (F.obj x) (F.obj z) =
      monicKPrismTracedRawComposition F f g := by
  change (_ ≫ RawSpectrumMapping.composition _ _ _) ≫ RawSpectrumMapping.post _ _ = _
  rw [Category.assoc, RawSpectrumMapping.composition_post, ← Category.assoc]
  change (_ ≫ (_ ⊗ₘ kRawMappingProjection (F.obj y) (F.obj z))) ≫ _ = _
  have h : lift (fst _ _ ≫ monicKPrismTracedBFFamily F f)
      (snd _ _ ≫ monicKPrismTracedBFFamily F g) ≫
        (𝟙 _ ⊗ₘ kRawMappingProjection (F.obj y) (F.obj z)) =
      lift (fst _ _ ≫ monicKPrismTracedBFFamily F f)
        (snd _ _ ≫ monicKPrismTracedRawFamily F g) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_snd_assoc,
        lift_fst, lift_snd, Category.comp_id, monicKPrismTracedBFFamily_projection]
  exact congrArg (· ≫ RawSpectrumMapping.composition _ _ _) h

/-- raw 合成族の各段は、同じ全パラメータの二つの評価の豊穣合成。 -/
lemma monicKPrismTracedRawComposition_evaluation (n : ℕ) :
    monicKPrismTracedRawComposition F f g ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n =
      lift (fst _ _ ≫ monicKPrismTracedBFFamily F f ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n)
        (snd _ _ ≫ monicKPrismTracedRawFamily F g ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj y)) (kKanSequence (F.obj z)) n) ≫
        eComp SSet ((kOmegaSpectrum (F.obj x)).level n).space
          ((kOmegaSpectrum (F.obj y)).level n).space ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKPrismTracedRawComposition, Category.assoc, RawSpectrumMapping.composition_evaluation]
  dsimp only [RawSpectrumMapping.compositionFamily]
  rw [← Category.assoc]
  congr 1

/-- 二本の族の raw 合成を元の合成射と結ぶ、全区間を持つ実補正列。 -/
def monicKPrismTracedCompositeCorrectionChain (n : ℕ) :
    FamilyHomotopyChain
      (SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)))
      (monicKPrismTracedRawComposition F f g ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  let a := fst P Q ≫ monicKPrismTracedBFFamily F f ≫
    OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n
  let b := snd P Q ≫ monicKPrismTracedRawFamily F g ≫
    RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj y)) (kKanSequence (F.obj z)) n
  let cf := familyHomotopyChainPrecomp (fst P Q) (monicKPrismTracedStage F f n).chain
  let cg := familyHomotopyChainPrecomp (snd P Q) (monicKPrismTracedStage F g n).chain
  have hf : fst P Q ≫ (monicKPrismTracedStage F f n).val =
      a ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
        ((monicKKanSequenceProjection (F.obj y)).app n)).right := by
    dsimp only [a]
    simpa only [Category.assoc, monicKPrismTracedStage] using congrArg (fun h => fst P Q ≫ h)
      (monicKPrismTracedBFFamily_evaluation F f n).symm
  have hg : snd P Q ≫ (monicKPrismTracedStage F g n).val = b := by
    dsimp only [b]
    rw [monicKPrismTracedRawFamily_evaluation]
  let cf' := familyHomotopyChainTargetTransport cf hf
  let cg' := familyHomotopyChainTargetTransport cg hg
  have hsf : SSet.const (X := P ⊗ Q) (familyVertex (monicKToRawLevelMap (F.map f) n)) =
      fst P Q ≫ monicKPrismRawLevelFamily n F f := by
    rw [monicKPrismRawLevelFamily, SSet.comp_const]
  have hsg : SSet.const (X := P ⊗ Q)
      (familyVertex ((monicKKanSequenceProjection (F.obj y)).app n ≫
        kKanSequenceLevelMap (F.map g) n)) = snd P Q ≫ monicKPrismRawLevelFamily n F g := by
    rw [monicKPrismRawLevelFamily, SSet.comp_const]
    rfl
  let c := pointedCompositeCorrectionChain ((monicKKanSequenceProjection (F.obj y)).app n)
    (kKanSequenceLevelMap (F.map g) n) (monicKToRawLevelMap (F.map f) n) a b
    (familyHomotopyChainSourceTransport cf' hsf) (familyHomotopyChainSourceTransport cg' hsg)
  have hs : monicKToRawLevelMap (F.map (f ≫ g)) n =
      monicKToRawLevelMap (F.map f) n ≫ kKanSequenceLevelMap (F.map g) n := by
    rw [F.map_comp]
    simp only [monicKToRawLevelMap, kKanSequenceLevelMap_comp, Category.assoc]
  exact familyHomotopyChainSourceTransport
    (familyHomotopyChainTargetTransport c (monicKPrismTracedRawComposition_evaluation F f g n).symm)
    (congrArg (fun h => SSet.const (X := P ⊗ Q) (familyVertex h)) hs)

end SerrePositivity.KST.SConstruction
