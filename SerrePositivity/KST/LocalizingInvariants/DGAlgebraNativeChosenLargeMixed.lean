module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenFrameKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition

/-!
概要：元の二つの実混合比較を、大宇宙の同じ Kan 共通標的への自然変換にする。
方針：共通混合 Hom の実 Kan 置換単位を後合成し、同じ射を持ち上げる。
規約：追加の同値仮定・モデル構造入力なし。比較は全標的射に自然。
使われ方：選んだ right resolution と実始域 frame 図式の全自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.InfinityCategories SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def nativeCellChosenMixedLeftToKan : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⟶
    nativeCellChosenMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement :=
  nativeCellChosenMixedLeft R A ≫
    Functor.whiskerLeft (nativeCellChosenMixedMappingFunctor R A) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit

def nativeCellChosenMixedRightToKan : nativeCellChosenRightMappingFunctor R A ⟶
    nativeCellChosenMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement :=
  nativeCellChosenMixedRight R A ≫
    Functor.whiskerLeft (nativeCellChosenMixedMappingFunctor R A) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit

lemma nativeCellChosenMixedLeftToKan_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellChosenMixedLeftToKan R A).app B) :=
  (nativeCellChosenMixedLeft_weakEquivalence R A B).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

lemma nativeCellChosenMixedRightToKan_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellChosenMixedRightToKan R A).app B) :=
  (nativeCellChosenMixedRight_weakEquivalence R A B).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

def nativeCellChosenMixedLeftLarge :
    nativeCellSourceFrameLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellChosenMixedReplacementLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellChosenMixedLeftToKan R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellChosenMixedRightLarge :
    nativeCellChosenRightLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellChosenMixedReplacementLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellChosenMixedRightToKan R A) SSet.uliftFunctor.{u + 1, u}

lemma nativeCellChosenMixedLeftLarge_isQCatEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((nativeCellSourceFrameLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellChosenMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellChosenMixedLeftLarge R A).app B) := by
  have := nativeCellSourceFrameHom_kanComplex R A B
  have : SSet.KanComplex ((nativeCellChosenMixedMappingFunctor R A ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_kanComplex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellChosenMixedLeftToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

lemma nativeCellChosenMixedRightLarge_isQCatEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((nativeCellChosenRightLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellChosenMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellChosenMixedRightLarge R A).app B) := by
  have : SSet.KanComplex ((nativeCellChosenRightMappingFunctor R A).obj B) :=
    nativeCellChosenRightMapping_kanComplex R A B
  have : SSet.KanComplex ((nativeCellChosenMixedMappingFunctor R A ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_kanComplex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellChosenMixedRightToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
