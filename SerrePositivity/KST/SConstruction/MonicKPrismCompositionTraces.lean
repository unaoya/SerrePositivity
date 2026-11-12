module
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositionFamilies

/-! # 元の K 合成族の補正全区間の二つの部分
概要：合成族の補正列を、前の射の補正と後ろの射の補正の実 trace へ厳密に分解する。
方針：構成した補正列の前後合成・積・連結の trace を計算する。
規約：全精密化パラメータと全時刻の区間を保持する。
使われ方：構造射で射影した合成補正と元の合成面の比較。
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
local instance prismCompositionTraceSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 合成補正の前半は、前の射の元の全補正を元の後続射で後合成した区間。 -/
def monicKPrismCompositeFirstTrace (n : ℕ) :
    List ((nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right) :=
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map
    (fun h => (fst P Q ▷ (Δ[1] : SSet.{u})) ≫ h ≫
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
        (kKanSequenceLevelMap (F.map g) n)).right)

/-- 合成補正の後半は、後ろの元の全補正を前の同じ BF 族と合成した区間。 -/
def monicKPrismCompositeSecondTrace (n : ℕ) :
    List ((nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right) :=
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  (familyHomotopyChainTrace (monicKPrismTracedStage F g n).chain).map (fun h =>
    lift (fst (P ⊗ Q) (Δ[1] : SSet.{u}) ≫ fst P Q ≫ monicKPrismTracedBFFamily F f ≫
      OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n)
      ((snd P Q ▷ (Δ[1] : SSet.{u})) ≫ h) ≫
        eComp SSet ((kOmegaSpectrum (F.obj x)).level n).space
          ((kOmegaSpectrum (F.obj y)).level n).space ((kKanSequence (F.obj z)).level n).space)

/-- 合成補正の実 trace は、二本の元の補正全区間の順序付き連結そのもの。 -/
lemma monicKPrismTracedCompositeCorrectionChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g n) =
      monicKPrismCompositeFirstTrace F f g n ++ monicKPrismCompositeSecondTrace F f g n := by
  simp only [monicKPrismTracedCompositeCorrectionChain, familyHomotopyChainSourceTransport_trace,
    familyHomotopyChainTargetTransport_trace, pointedCompositeCorrectionChain_trace,
    familyHomotopyChainPrecomp_trace, List.map_map, Function.comp_def,
    monicKPrismCompositeFirstTrace, monicKPrismCompositeSecondTrace, Category.assoc]
  rfl

/-- 合成族の指定頂点は、先に選んだ同じ二つの BF 境界の実合成を回収する。 -/
lemma monicKPrismTracedCompositionFamily_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g)) ≫
      monicKPrismTracedCompositionFamily F f g =
      lift (fst (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ monicKPrismTracedBFBoundary F f)
        (snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ monicKPrismTracedBFBoundary F g) ≫
          OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj x))
            (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z)) := by
  rw [monicKPrismTracedCompositionFamily, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, lift_fst, lift_snd, tensorHom_fst_assoc, tensorHom_snd_assoc,
      monicKPrismTracedBFFamily_boundary]

/-- 零段の合成補正には実区間がなく、元の段を変更しない。 -/
lemma monicKPrismTracedCompositeCorrectionChain_zero_trace :
    familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g 0) = [] := by
  rw [monicKPrismTracedCompositeCorrectionChain_trace]
  rfl

/-- 合成族の零段の raw 評価は、元の合成射の段の定数族そのものである。 -/
lemma monicKPrismTracedRawComposition_zero :
    monicKPrismTracedRawComposition F f g ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) 0 =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  (familyHomotopyChain_eq_of_trace_nil (monicKPrismTracedCompositeCorrectionChain F f g 0)
    (monicKPrismTracedCompositeCorrectionChain_zero_trace F f g)).symm

end SerrePositivity.KST.SConstruction
