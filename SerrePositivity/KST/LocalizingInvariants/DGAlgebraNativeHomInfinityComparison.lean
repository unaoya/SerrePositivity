module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSpecifiedFrameCoherentSource
public import SerrePositivity.EInfinity.DGAlgebra.HomInfinityComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の実 AW 全標的図式を、指定した全擬同型局所化の共変 Hom と比較する。
方針：E2-S (7) の段六の全図式比較を合成し、実源同型の順逆を相殺する。
規約：比較・モデル・分解の存在を仮定入力にせず、同じ指定二胞体を使う。
使われ方：β6 f4c の実導来比較と f4d の元の Postnikov 全錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))
attribute [local instance] EInfinity.DGAlgebra.modelCategory

/-- 実選択 right frame の全標的図式は、元の指定局所化の同じ共変 Hom と同型。 -/
def nativeCellChosenRightHomInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) := by
  let a := nativeModelInfinityPresentationIso R
  let G := nativeModelQuasiIsoInfinityMap R
  let e := nativeCellChosenRightHammockIso R A ≪≫
    (EInfinity.DGAlgebra.frameTerminalHomIso R G
      (nativeModelQuasiIsoInfinity_isLocalization R) (cellResolution R A)).precomp
        ((SSet.uliftFunctor.{u + 2, u + 1}).map a.inv)
  have hq : a.inv ≫ G = quasiIsoInfinityMap R := by
    change a.inv ≫ (a.hom ≫ quasiIsoInfinityMap R) = _
    rw [← Category.assoc, a.inv_hom_id, Category.id_comp]
  have ht : (SSet.uliftFunctor.{u + 2, u + 1}).map a.inv ≫
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)) := by
    rw [← Category.assoc, ← Functor.map_comp, hq]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e rfl ht

/-- 元の AW 模型の全高次標的自然性を保つ、実導来 Hom 比較。 -/
def multiplicativeCellMappingHomInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingInfinityCoherent R A)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) :=
  multiplicativeCellMappingChosenRightCoherentIso R A ≪≫ nativeCellChosenRightHomInfinityIso R A

/-- 指定局所化 Hom への全比較に送った、元の ordinary Hom 単位。
全標的の同じ自然変換を使い、指定底の点を別に選ばない。 -/
def nativeCellHomInfinityCoherentUnit :
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellOrdinaryInfinityKanFunctor R A))) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :=
  nativeCellChosenRightMappingCoherentUnit R A ≫ (nativeCellChosenRightHomInfinityIso R A).hom

/-- 元の AW 単位は、同じ全自然比較で指定局所化の同じ単位へ写る。
任意の標的図式・指定底への制限にも同じ等式を前合成できる。 -/
lemma nativeCellMappingHomInfinityCoherentUnit :
    nativeCellMappingCoherentUnit R A ≫ (multiplicativeCellMappingHomInfinityIso R A).hom =
      nativeCellHomInfinityCoherentUnit R A := by
  change nativeCellMappingCoherentUnit R A ≫
    ((multiplicativeCellMappingChosenRightCoherentIso R A).hom ≫
      (nativeCellChosenRightHomInfinityIso R A).hom) = _
  rw [← Category.assoc, nativeCellMappingCoherentUnit_chosenRight]
  rfl

/-- 全元射の単位を保つ同じ Hom 比較を、全図式のホモトピー圏の under 同型に束ねる。 -/
def nativeCellPointedHomInfinityIso :
    Under.mk (nativeCellMappingCoherentUnit R A) ≅
      Under.mk (nativeCellHomInfinityCoherentUnit R A) :=
  Under.isoMk (multiplicativeCellMappingHomInfinityIso R A)
    (nativeCellMappingHomInfinityCoherentUnit R A)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
