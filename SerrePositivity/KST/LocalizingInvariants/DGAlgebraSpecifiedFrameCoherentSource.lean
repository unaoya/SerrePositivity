module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSpecifiedFrameComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeCoherentUnits

/-!
概要：選択 right frame の元の全標的図式を、E2 の六辺の全図式比較へ接続する。
方針：同じ Ex∞ 単位を全自然変換として実現し、実源同型で前合成する。
規約：点ごとの逆を選ばず、元の ULiftHom 提示上の全単体を保持する。
使われ方：E2-S (7) の終端接続を元の実 AW 全図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))
attribute [local instance] EInfinity.DGAlgebra.modelCategory
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex

/-- 六辺の始点を、元の全標的提示へ同じ関手で制限する。 -/
def nativeCellFrameInitialKanFunctor : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  (ULiftHom.down ⋙ AsSmall.up) ⋙
    EInfinity.FrameHom.rightFrameHammockKanDiagram
      ((EInfinity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
      (EInfinity.DGAlgebra.rightFrameFamily R) 0

/-- 元の選択 right Hom から六辺の始点への同じ全自然な Ex∞ 単位。 -/
def nativeCellFrameInitialUnit :
    nativeCellChosenRightInfinityKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      nativeCellFrameInitialKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget where
  app B := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
    (((nativeCellChosenRightInfinityKanFunctor R A).obj B).obj)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality
    ((nativeCellChosenRightInfinityKanFunctor R A).map f)

/-- 同じ全自然な単位の各成分は実 right Hom の Kan 性による同値。 -/
lemma nativeCellFrameInitialUnit_isQCatEquivalence (B : InfinityPresentation R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((nativeCellChosenRightInfinityKanFunctor R A).obj B).obj)
      (Y := ((nativeCellFrameInitialKanFunctor R A).obj B).obj)
      ((nativeCellFrameInitialUnit R A).app B) := by
  have := cellResolution_isCofibrant R A
  exact (EInfinity.FrameHom.rightFrameHomExUnitEquivalence
    (X := cellResolution R A) (EInfinity.DGAlgebra.rightFrameFamily R) B.objDown).isQCatEquivalence

/-- 六辺への接続は元の全提示上で一つの関手同型。 -/
def nativeCellChosenRightFrameSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (nativeModelInfinityPresentationIso R).inv ≫
        EInfinity.FrameHom.rightFrameHammockCoherentDiagram
          ((EInfinity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
          (EInfinity.DGAlgebra.rightFrameFamily R) 0) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨nativeCellChosenRightInfinityKanFunctor R A, trivial⟩)
    (G := ⟨nativeCellFrameInitialKanFunctor R A, trivial⟩)
    (nativeCellFrameInitialUnit R A) (nativeCellFrameInitialUnit_isQCatEquivalence R A)

/-- E2 の六辺の終端まで、元の全標的提示上で比較する。 -/
def nativeCellChosenRightHammockIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (nativeModelInfinityPresentationIso R).inv ≫
        EInfinity.FrameHom.rightFrameHammockCoherentDiagram
          ((EInfinity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
          (EInfinity.DGAlgebra.rightFrameFamily R) 6) :=
  nativeCellChosenRightFrameSourceIso R A ≪≫
    (nativeCellFrameHammockCoherentComparison R A).precomp
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (nativeModelInfinityPresentationIso R).inv)

/-- 元の AW 全図式も、同じ元の提示上で六辺の終端まで比較する。 -/
def multiplicativeCellMappingHammockCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingInfinityCoherent R A)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (nativeModelInfinityPresentationIso R).inv ≫
        EInfinity.FrameHom.rightFrameHammockCoherentDiagram
          ((EInfinity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
          (EInfinity.DGAlgebra.rightFrameFamily R) 6) :=
  multiplicativeCellMappingChosenRightCoherentIso R A ≪≫ nativeCellChosenRightHammockIso R A

/-- 全 ordinary Hom 単位の指定比較は、六辺を全図式で合成しても保持される。 -/
lemma nativeCellMappingCoherentUnit_hammock :
    nativeCellMappingCoherentUnit R A ≫ (multiplicativeCellMappingHammockCoherentIso R A).hom =
      nativeCellChosenRightMappingCoherentUnit R A ≫ (nativeCellChosenRightHammockIso R A).hom := by
  change nativeCellMappingCoherentUnit R A ≫
    ((multiplicativeCellMappingChosenRightCoherentIso R A).hom ≫
      (nativeCellChosenRightHammockIso R A).hom) = _
  rw [← Category.assoc, nativeCellMappingCoherentUnit_chosenRight]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
