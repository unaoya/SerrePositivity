module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEdgewiseFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningCandidate
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftCoherentTransportReconstruction

/-!
概要：strict な Kan 値図式と値を反転した図式の coherent な関手同型。
方針：edgewise 解像の左右の自然変換を関手空間の同型へ写して合成する。
規約：対象ごとの任意の同値ではなく、図式全体の自然な共通解像を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening 候補の係数反転の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Kan 値図式の edgewise 解像の coherent な表示は元の図式と関手同型。
方針：右の自然変換の各成分の trivial Kan fibration 性を用いる。
規約：順方向は右射影の実現。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、係数反転の共通比較の右側。 -/
noncomputable def kanDiagramEdgewiseRightIso {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseFunctor, trivial⟩) (G := ⟨F, trivial⟩)
    (Functor.whiskerRight (Functor.whiskerLeft F _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseRight) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (F.obj c).obj))

/-- 概要：Kan 値図式の edgewise 解像の coherent な表示は反転した図式と関手同型。
方針：左の自然変換の各成分の trivial Kan fibration 性を用いる。
規約：順方向は左射影の実現。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、係数反転の共通比較の左側。 -/
noncomputable def kanDiagramEdgewiseLeftIso {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseFunctor, trivial⟩) (G := ⟨F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor, trivial⟩)
    (Functor.whiskerRight (Functor.whiskerLeft F _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseLeft) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (F.obj c).obj))

/-- 概要：strict な Kan 値図式と値を反転した図式の coherent な表示は関手同型。
方針：共通の edgewise 解像からの二つの関手同型を合成する。
規約：底の圏とその射は変えない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の係数規約を図式全体で接続する。 -/
noncomputable def kanDiagramOppositeComparisonIso {C : Type u} [Category.{u} C]
    (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)) :=
  (kanDiagramEdgewiseRightIso F).symm ≪≫ kanDiagramEdgewiseLeftIso F

/-- 概要：straightening 候補と反転係数による coherent transport は関手同型。
方針：strict transport 図式に edgewise の係数反転の比較を適用する。
規約：二つの候補を厳密な等式で同一視しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、反転係数での復元を既存の候補へ移す。 -/
noncomputable def leftStraighteningCandidateCoherentTransportIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) :=
  kanDiagramOppositeComparisonIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
