module

public import SerrePositivity.KST.NonConnective.SingleBoundaryMiddle
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor
public import SerrePositivity.KST.Spectra.SpectrumFiberStage

/-!
概要：元の連結 BF K の非負整数群と、同じ一重 S• 境界商の正次数群。
方針：BF の一段表示と同じ単射置換射影の群同型を合成する。
規約：零次も同じ公式で扱う。使われ方：固定 dg K への加法性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 非負整数 n は BF の一段では正次数 n+1。 -/
lemma nonnegativeBoundary_degree (n : ℕ) : OmegaSpectrum.degree (n : ℤ) 1 = n + 1 := by
  unfold OmegaSpectrum.degree
  omega

/-- 同じ BF の一段表示を、単射置換列の段として固定する。 -/
def nonnegativeBoundaryStage (X : StableModel.{u}) (n : ℕ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) (n : ℤ) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((monicKKanSequence X).level 1).space.right n
        ((monicKKanSequence X).level 1).space.basepoint :=
  OmegaSpectrum.positiveStageEquiv (kOmegaSpectrum X) (n : ℤ) 1 n
    (by omega) (nonnegativeBoundary_degree n)

/-- 同じ一段表示の自然性。 -/
lemma nonnegativeBoundaryStage_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) (n : ℤ)) :
    nonnegativeBoundaryStage Y n (kHomotopyMap f (n : ℤ) a) =
      pointedGroupMap n ((monicKKanSequenceMap f).app 1) (nonnegativeBoundaryStage X n a) :=
  OmegaSpectrum.positiveStageEquiv_natural (kSpectrumMap f) (n : ℤ) 1 n
    (by omega) (nonnegativeBoundary_degree n) a

/-- 同じ射影を、元の一重境界商を明示した点つき射として保持する。 -/
def monicBoundaryProjection (X : StableModel.{u}) :
    ((monicKKanSequence X).level 1).space ⟶ (boundaryKanRealizationFunctor 0).obj X :=
  (monicKKanSequenceProjection X).app 1

/-- 同じ射影の全基点 π 同型。 -/
lemma monicBoundaryProjection_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (monicBoundaryProjection X).right :=
  monicKKanSequenceProjection_piIsomorphism X 1

/-- 同じ射影は、元の完全射に関して同じ基点固定成分で自然。 -/
lemma monicBoundaryProjection_component {X Y : StableModel.{u}} (f : X ⟶ Y) :
    PointedMapping.componentOf ((monicKKanSequenceMap f).app 1 ≫ monicBoundaryProjection Y) =
      PointedMapping.componentOf
        (monicBoundaryProjection X ≫ (boundaryKanRealizationFunctor 0).map f) :=
  monicKKanSequenceMap_projection_component f 1

/-- 同じ単射置換の一段から、元の一重境界商への群同型。 -/
def monicBoundaryGroupEquiv (X : StableModel.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((monicKKanSequence X).level 1).space.right n
        ((monicKKanSequence X).level 1).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj X).right n
        ((boundaryKanRealizationFunctor 0).obj X).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (monicBoundaryProjection X).right
    (monicBoundaryProjection_piIsomorphism X)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (monicBoundaryProjection X))

/-- 同じ比較の順方向は元の射影の群作用そのもの。 -/
lemma monicBoundaryGroupEquiv_apply (X : StableModel.{u}) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((monicKKanSequence X).level 1).space.right n
      ((monicKKanSequence X).level 1).space.basepoint) :
    monicBoundaryGroupEquiv X n a =
      pointedGroupMap n (monicBoundaryProjection X) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply n (monicBoundaryProjection X).right
    (monicBoundaryProjection_piIsomorphism X)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (monicBoundaryProjection X)) a

/-- 同じ単射置換射影の群比較は、元の完全射について自然。 -/
lemma monicBoundaryGroupEquiv_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((monicKKanSequence X).level 1).space.right n
      ((monicKKanSequence X).level 1).space.basepoint) :
    monicBoundaryGroupEquiv Y n (pointedGroupMap n ((monicKKanSequenceMap f).app 1) a) =
      singleBoundaryGroupMap f n (monicBoundaryGroupEquiv X n a) := by
  rw [monicBoundaryGroupEquiv_apply, monicBoundaryGroupEquiv_apply]
  change pointedGroupMap n (monicBoundaryProjection Y)
      (pointedGroupMap n ((monicKKanSequenceMap f).app 1) a) =
    pointedGroupMap n ((boundaryKanRealizationFunctor 0).map f)
      (pointedGroupMap n (monicBoundaryProjection X) a)
  rw [← pointedGroupMap_comp, ← pointedGroupMap_comp]
  exact congrFun (pointedHomotopyMap_eq_of_component
    (monicBoundaryProjection_component f) (n + 1)) a

/-- 同じ連結 BF K の非負整数群を、同じ一重境界商の群で表示する。 -/
def nonnegativeBoundaryEquiv (X : StableModel.{u}) (n : ℕ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) (n : ℤ) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj X).right n
        ((boundaryKanRealizationFunctor 0).obj X).basepoint :=
  (nonnegativeBoundaryStage X n).trans (monicBoundaryGroupEquiv X n)

/-- この同じ群表示は、元の完全射の K 作用について自然。 -/
lemma nonnegativeBoundaryEquiv_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) (n : ℤ)) :
    nonnegativeBoundaryEquiv Y n (kHomotopyMap f (n : ℤ) a) =
      singleBoundaryGroupMap f n (nonnegativeBoundaryEquiv X n a) := by
  simp only [nonnegativeBoundaryEquiv, MulEquiv.trans_apply,
    nonnegativeBoundaryStage_naturality, monicBoundaryGroupEquiv_naturality]

end SerrePositivity.KST.NonConnective
