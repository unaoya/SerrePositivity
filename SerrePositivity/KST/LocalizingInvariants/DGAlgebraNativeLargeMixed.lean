module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition

/-!
概要：元の二つの実混合比較を、大宇宙の同じ Kan 共通標的への自然変換にする。
方針：共通混合 Hom の実 Kan 置換単位を後合成し、同じ射を持ち上げる。
規約：追加の同値仮定・モデル構造入力なし。比較は全標的射に自然。
使われ方：元の AW 空間値図式と実始域 frame 図式の全自然同型。
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

def nativeCellMixedLeftToKan : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⟶
    nativeCellMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement :=
  nativeCellMixedLeft R A ≫
    Functor.whiskerLeft (nativeCellMixedMappingFunctor R A) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit

def nativeCellMixedRightToKan : multiplicativeMappingFunctor R (cellResolution R A) ⟶
    nativeCellMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement :=
  nativeCellMixedRight R A ≫
    Functor.whiskerLeft (nativeCellMixedMappingFunctor R A) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit

lemma nativeCellMixedLeftToKan_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellMixedLeftToKan R A).app B) :=
  (nativeCellMixedLeft_weakEquivalence R A B).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

lemma nativeCellMixedRightToKan_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellMixedRightToKan R A).app B) :=
  (nativeCellMixedRight_weakEquivalence R A B).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _)

def nativeCellMixedLeftLarge :
    nativeCellSourceFrameLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellMixedReplacementLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellMixedLeftToKan R A) SSet.uliftFunctor.{u + 1, u}

def nativeCellMixedRightLarge :
    multiplicativeCellMappingLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellMixedReplacementLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (nativeCellMixedRightToKan R A) SSet.uliftFunctor.{u + 1, u}

lemma nativeCellMixedLeftLarge_isQCatEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((nativeCellSourceFrameLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellMixedLeftLarge R A).app B) := by
  have := nativeCellSourceFrameHom_kanComplex R A B
  have : SSet.KanComplex ((nativeCellMixedMappingFunctor R A ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_kanComplex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellMixedLeftToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

lemma nativeCellMixedRightLarge_isQCatEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((multiplicativeCellMappingLargeKanFunctor R A).obj B).obj ⟶
        ((nativeCellMixedReplacementLargeKanFunctor R A).obj B).obj from
          (nativeCellMixedRightLarge R A).app B) := by
  have : SSet.KanComplex ((multiplicativeMappingFunctor R (cellResolution R A)).obj B) :=
    multiplicativeCellMapping_kanComplex R A B
  have : SSet.KanComplex ((nativeCellMixedMappingFunctor R A ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_kanComplex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (nativeCellMixedRightToKan_weakEquivalence R A B).isSimplicialHomotopyEquivalence)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
