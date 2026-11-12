module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeLargeMixed
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeCoherent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：元の AW 写像模型と実始域 frame の全標的図式を coherent に比較する。
方針：同じ混合 Hom の Kan 置換への二つの自然変換を関手同型へ移す。
規約：比較は全単体の図式上で行い、指定局所化との比較を仮定しない。
使われ方：E2-S (6) の二胞体を保つ導来 Hom 比較への接続。
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

/-- 概要：dg 代数の Kan 値比較を同じ ULiftHom 提示上で実現する。
方針：元の自然変換を前合成して F1 の全図式比較へ渡す。
規約：公開の native 特殊化には F・G・η・hη を仮定入力として残さない。
使われ方：実 AW と実始域 frame の二つの比較の組み立て。 -/
def nativeMixedPresentationIso
    (F G : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1})
    (η : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ B, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj B).obj) (Y := (G.obj B).obj) (η.app B)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve ((ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve ((ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ G)) := by
  let θ : ((ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ F) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      ((ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ G) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
    { app B := η.app B.objDown
      naturality B C f := η.naturality f.down }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨(ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ F, trivial⟩)
    (G := ⟨(ULiftHom.down : InfinityPresentation R ⥤ _) ⋙ G, trivial⟩)
    θ (fun B => hη B.objDown)

def nativeCellMixedLeftCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellMixedReplacementInfinityKanFunctor R A)) :=
  nativeMixedPresentationIso R
    (nativeCellSourceFrameLargeKanFunctor R A) (nativeCellMixedReplacementLargeKanFunctor R A)
    (nativeCellMixedLeftLarge R A) (nativeCellMixedLeftLarge_isQCatEquivalence R A)

def nativeCellMixedRightCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingInfinityCoherent R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellMixedReplacementInfinityKanFunctor R A)) :=
  nativeMixedPresentationIso R
    (multiplicativeCellMappingLargeKanFunctor R A) (nativeCellMixedReplacementLargeKanFunctor R A)
    (nativeCellMixedRightLarge R A) (nativeCellMixedRightLarge_isQCatEquivalence R A)

def multiplicativeCellMappingSourceFrameCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingInfinityCoherent R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A)) :=
  nativeCellMixedRightCoherentIso R A ≪≫ (nativeCellMixedLeftCoherentIso R A).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
