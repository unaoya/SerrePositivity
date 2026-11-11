module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionStageTriangles
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositionTraces

/-! # 元の合成補正全区間の直通列点での二部分
概要：二入力の合成補正の全 trace を、前後二本の元の全区間の像へ厳密に展開する。
方針：元の二射影を直通列点で評価し、同じ全円柱の前合成と豊穣合成を回収する。
規約：全区間と順序を保持し、両部分の代表を選び直さない。
使われ方：三入力の左右合成補正の全辺路を交換正方形で照合する。
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
local instance compositePointTracePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の単一入力の全補正区間を、同じ直通列点で評価した全 trace。 -/
def monicKPrismUnaryPointTrace (n : ℕ) :=
  (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫ ·)

variable {z : I} (g : y ⟶ z)

/-- 前の元の全補正を、元の後続射で後合成した同じ全区間列。 -/
def monicKPrismCompositePointFirstTrace (n : ℕ) :=
  (monicKPrismUnaryPointTrace F f n).map
    (· ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
      (kKanSequenceLevelMap (F.map g) n)).right)

/-- 後の元の全補正を、元の前の BF 境界射と合成した同じ全区間列。 -/
def monicKPrismCompositePointSecondTrace (n : ℕ) :
    List ((Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right) :=
  (monicKPrismUnaryPointTrace F g n).map (fun h =>
    lift (fst (Δ[0] : SSet.{u}) Δ[1] ≫ monicKPrismTracedBFBoundary F f ≫
      OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n) h ≫
        eComp SSet ((kOmegaSpectrum (F.obj x)).level n).space
          ((kOmegaSpectrum (F.obj y)).level n).space ((kKanSequence (F.obj z)).level n).space)

/-- 元の第一 trace の直通列制限は、元の前の単一射の同じ全区間の後合成列。 -/
lemma monicKPrismCompositeFirstTrace_point (n : ℕ) :
    (monicKPrismCompositeFirstTrace F f g n).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
          (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) =
      monicKPrismCompositePointFirstTrace F f g n := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
      fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) := by
    rw [compositionStringPair_first, compositionStringFirst_direct]
  simp only [monicKPrismCompositeFirstTrace, monicKPrismCompositePointFirstTrace,
    monicKPrismUnaryPointTrace, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro h _
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun q => (q ▷ (Δ[1] : SSet.{u})) ≫ h ≫
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
        (kKanSequenceLevelMap (F.map g) n)).right) hp

/-- 元の第二 trace の直通列制限は、後の単一射の同じ全区間と前の BF 境界の合成列。 -/
lemma monicKPrismCompositeSecondTrace_point (n : ℕ) :
    (monicKPrismCompositeSecondTrace F f g n).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
          (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) =
      monicKPrismCompositePointSecondTrace F f g n := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
      fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) := by
    rw [compositionStringPair_first, compositionStringFirst_direct]
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
      snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) := by
    rw [compositionStringPair_second, compositionStringSecond_direct]
  have hf := (congrArg (· ≫ monicKPrismTracedBFFamily F f) hp).trans
    (monicKPrismTracedBFFamily_boundary F f)
  simp only [monicKPrismCompositeSecondTrace, monicKPrismCompositePointSecondTrace,
    monicKPrismUnaryPointTrace, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro h _
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc, comp_lift]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lift_fst]
    simpa only [Category.assoc, whiskerRight_fst_assoc] using
      congrArg (fun q => fst (Δ[0] : SSet.{u}) Δ[1] ≫ q ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n) hf
  · simp only [lift_snd]
    simpa only [comp_whiskerRight, Category.assoc] using
      congrArg (fun q => (q ▷ (Δ[1] : SSet.{u})) ≫ h) hq

end SerrePositivity.KST.SConstruction
