module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenLargeMixed
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameCoherent

/-!
概要：実 AW 模型を、E2 の強い rightFrameHom の全標的図式へ比較する。
方針：二つの right frame を同じ実始域 frame に混合比較して合成する。
規約：増大の条件を混同せず、全ての分解と比較の証拠を実供給する。
使われ方：E2-S (6) の選んだ right resolution の比較を元の AW 模型へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def nativeCellChosenMixedLeftCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenMixedReplacementInfinityKanFunctor R A)) :=
  nativeMixedPresentationIso R
    (nativeCellSourceFrameLargeKanFunctor R A)
    (nativeCellChosenMixedReplacementLargeKanFunctor R A)
    (nativeCellChosenMixedLeftLarge R A) (nativeCellChosenMixedLeftLarge_isQCatEquivalence R A)

def nativeCellChosenMixedRightCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenMixedReplacementInfinityKanFunctor R A)) :=
  nativeMixedPresentationIso R
    (nativeCellChosenRightLargeKanFunctor R A)
    (nativeCellChosenMixedReplacementLargeKanFunctor R A)
    (nativeCellChosenMixedRightLarge R A) (nativeCellChosenMixedRightLarge_isQCatEquivalence R A)

def nativeCellChosenMappingSourceFrameCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A)) :=
  nativeCellChosenMixedRightCoherentIso R A ≪≫ (nativeCellChosenMixedLeftCoherentIso R A).symm

def multiplicativeCellMappingChosenRightCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingInfinityCoherent R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A)) :=
  multiplicativeCellMappingSourceFrameCoherentIso R A ≪≫
    (nativeCellChosenMappingSourceFrameCoherentIso R A).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
