module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatCoherentPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalPullback

/-!
概要：元の QCat の後合成を、同じ対角評価の標準 Hom 比較に沿う引き戻しと比較する。
方針：厳密な可換四角形で比較射を作り、射影と全空間比較の同値性を使う。
規約：元の全体比較と元の後合成作用を保持する。
使われ方：同じ底上の二つの Kan fibration の fiber 比較へ進む。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable (A B Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f : B ⟶ Z)

/-- 元の内部 Hom の後合成の core を、分類先と同じ宇宙へ持ち上げる。 -/
def qCatPostcompositionMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom A B) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom A Z) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom A.obj).map (show B.obj ⟶ Z.obj from f)))

local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A Z

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_fibration
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_kanComplex

/-- 同じ対角評価を、元の標準 Hom 比較に沿って引き戻した全空間。 -/
def qCatPostcompositionPullback : SSet.{u + 1} := pullback q e

local instance : Quasicategory (qCatPostcompositionPullback A B Z f) := by
  unfold qCatPostcompositionPullback
  infer_instance

/-- 元の後合成と同じ底を持つ、元の coherent 全体比較からの射。 -/
def qCatPostcompositionPullbackComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom A B) ⟶
      qCatPostcompositionPullback A B Z f :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence A B Z f)
    (qCatPostcompositionMap A B Z f) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatCoherentCompositionCorrespondence_diagonal A B Z f)

/-- 同じ引き戻し比較の第一射影は、元の coherent 全体比較。 -/
lemma qCatPostcompositionPullbackComparison_fst :
    qCatPostcompositionPullbackComparison A B Z f ≫ pullback.fst q e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence A B Z f := pullback.lift_fst ..

/-- 同じ引き戻し比較の第二射影は、元の後合成作用。 -/
lemma qCatPostcompositionPullbackComparison_snd :
    qCatPostcompositionPullbackComparison A B Z f ≫ pullback.snd q e =
      qCatPostcompositionMap A B Z f := pullback.lift_snd ..

/-- 同じ引き戻しから元の合成三角形全体への射影は同値。 -/
lemma qCatPostcompositionPullback_fst_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pullback.fst q e) := by
  have he₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_isQCatEquivalence A Z
  have he := he₀.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanEquivalenceLifting_compositionCorrespondenceDiagonal _ _)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry q e)).isQCatEquivalence.comp
    he.isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pullbackSymmetry q e).hom ≫ pullback.snd e q) at h
  simpa only [pullbackSymmetry_hom_comp_snd] using h

/-- 元の後合成から同じ対角評価の引き戻しへの、同じ全体比較は同値。 -/
lemma qCatPostcompositionPullbackComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (qCatPostcompositionPullbackComparison A B Z f) := by
  apply (qCatPostcompositionPullback_fst_isQCatEquivalence A B Z f).cancel_right
  rw [qCatPostcompositionPullbackComparison_fst]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence_isQCatEquivalence A B Z f

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
