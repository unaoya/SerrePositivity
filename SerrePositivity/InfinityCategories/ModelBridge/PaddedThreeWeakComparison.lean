module

public import SerrePositivity.InfinityCategories.ModelBridge.PaddedForwardDiagramComparison
public import SerrePositivity.EInfinity.Hammock.WeakProperColimit
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PaddedComparisonRecovery

/-!
# 元の padded な全語の余極限への三列の弱同値比較

概要：元の paddedThreeComparison 自身が弱ホモトピー同値となる。
方針：元の自然変換の全成分の弱同値性を proper 余極限へ移し、既存の因子分解を使う。
規約：元の全語の filtered 性を仮定しない。元の三列の標準射への接続は後続。
使われ方：padding 比較ホモトピーによる元の三列の標準射の弱同値性。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedForwardColimitMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (colim.map (paddedForwardDiagramMap (graphDiagram (weakEquivalences C) X Y))) :=
  weakProperColimitMap _ (graphDiagram_proper (weakEquivalences C) X Y).paddedForward
    (graphDiagram_proper (weakEquivalences C) X Y).padding
    (paddedForwardDiagramMap_isWeakHomotopyEquivalence X Y cof)

include cof in
lemma paddedThreeComparison_isWeakHomotopyEquivalence : IsWeakHomotopyEquivalence
    (paddedThreeComparison (graphDiagram (weakEquivalences C) X Y)) := by
  let H := graphDiagram (weakEquivalences C) X Y
  have hi : IsWeakHomotopyEquivalence (paddedForwardColimitIso H).inv :=
    FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have hc := hi.comp (paddedForwardColimitMap_isWeakHomotopyEquivalence X Y cof)
  change IsWeakHomotopyEquivalence ((paddedForwardColimitIso H).inv ≫
    colimMap (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H))) at hc
  rw [paddedThreeComparison_fac] at hc
  exact hc

end SerrePositivity.EInfinity.Hammock
