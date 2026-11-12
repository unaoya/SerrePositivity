module
public import SerrePositivity.KST.SConstruction.MonicKPrismSequenceFamilies
public import SerrePositivity.KST.SConstruction.KTracedFamilyLifting

/-! # 元の全 K prism の指定境界を保つ BF 厳密化
概要：元の適合区間から一点上の補正列を先に構成し、同じ境界を保つ全精密化の BF 族を得る。
方針：元の段族と実適合円柱を trace 付き逐次厳密化へ渡し、実射影に沿って持ち上げる。
規約：境界の定数性も任意の既存 BF 射との同一性も仮定しない。
使われ方：合成列上の coherent な K 関手化への具体的な相対構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の適合円柱を指定頂点に制限して実構成した全段の境界補正列。 -/
def monicKPrismTracedBoundary :=
  canonicalTracedSequenceBoundaryData (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f)

/-- 構成した一点上の補正列を保つ、全精密化上の厳密な raw 写像族。 -/
def monicKPrismTracedRawFamily :=
  prescribedSequenceFamilyRectification (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f) (monicKPrismTracedBoundary F f)

/-- 元の補正列から先に選んだ一点上の BF 境界。 -/
def monicKPrismTracedBFBoundary :=
  (kTracedBoundaryLiftData (F.obj x) (F.obj y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f) (monicKPrismTracedBoundary F f)).val

/-- 元の全適合円柱を厳密化し、先に選んだ BF 境界を保持した全精密化族。 -/
def monicKPrismTracedBFFamily :=
  (kTracedFamilyLiftData (F.obj x) (F.obj y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f) (monicKPrismTracedBoundary F f)).val

/-- 全精密化の BF 族は、先に構成した同じ BF 境界を厳密に回収する。 -/
lemma monicKPrismTracedBFFamily_boundary :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ≫ monicKPrismTracedBFFamily F f =
      monicKPrismTracedBFBoundary F f :=
  kTracedFamilyLiftData_boundary _ _ _ _ _ _

/-- 全精密化の BF 族の射影は、元の補正列を保持する同じ raw 族。 -/
lemma monicKPrismTracedBFFamily_projection :
    monicKPrismTracedBFFamily F f ≫ kRawMappingProjection (F.obj x) (F.obj y) =
      monicKPrismTracedRawFamily F f :=
  kTracedFamilyLiftData_projection _ _ _ _ _ _

/-- BF 族の各段は、元の単射置換の射影後に同じ補正済み段を回収する。 -/
lemma monicKPrismTracedBFFamily_evaluation (n : ℕ) :
    monicKPrismTracedBFFamily F f ≫
      OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          ((monicKKanSequenceProjection (F.obj y)).app n)).right =
      (prescribedSequenceFamilyStage (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
        (fun n => monicKPrismRawLevelFamily n F f)
        (fun n => monicKPrismRawSequenceCompatibility n F f)
        (monicKPrismTracedBoundary F f) n).val := by
  rw [← kRawMappingProjection_evaluation, ← Category.assoc,
    monicKPrismTracedBFFamily_projection]
  exact prescribedSequenceFamilyRectification_evaluation _ _ _ _ _ _ n

/-- 各段の元の族から raw 評価への補正有限列は、実区間として保存される。 -/
lemma monicKPrismTracedRawFamily_chain (n : ℕ) :
    Nonempty (FamilyHomotopyChain (monicKPrismRawLevelFamily n F f)
      (monicKPrismTracedRawFamily F f ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) n)) := by
  change Nonempty (FamilyHomotopyChain _
    (prescribedSequenceFamilyRectification _ _ _ _ _ _ ≫ _))
  rw [prescribedSequenceFamilyRectification_evaluation]
  exact ⟨(prescribedSequenceFamilyStage (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (fun n => monicKPrismRawLevelFamily n F f)
    (fun n => monicKPrismRawSequenceCompatibility n F f)
    (monicKPrismTracedBoundary F f) n).chain⟩

/-- 零段の raw 評価は元の段族を厳密に保持する。 -/
lemma monicKPrismTracedRawFamily_zero :
    monicKPrismTracedRawFamily F f ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) 0 =
      monicKPrismRawLevelFamily 0 F f :=
  prescribedSequenceFamilyRectification_zero _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
