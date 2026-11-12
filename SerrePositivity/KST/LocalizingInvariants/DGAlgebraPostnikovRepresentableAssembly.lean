module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMappingDescentLimit
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellTestCriterion
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeHomInfinityComparison

/-!
概要：実 cell 写像関手の表現可能比較を、元の Postnikov 錐の判定へ適用する。
方針：全標的 FunctorIso を元の錐全体へ前合成し、実試験錐の極限性を輸送する。
規約：E2-S (7) の実全図式比較を使い、比較の存在を公開仮定にしない。
使われ方：β6 f4d の元の局所化 Postnikov 錐の極限性。
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

private def nativeRepresentableComparison_of_frameComparison
    (R : Type u) [CommRing R] (A : Mon (Complex R))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingLocalizationFunctor R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) :=
  localizationFactorizationIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
    (multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫ e)

private lemma nativeRepresentableComparison_precomp
    (R : Type u) [CommRing R] (A : Mon (Complex R))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (nativeRepresentableComparison_of_frameComparison R A e)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R)) =
        multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫ e := by
  apply Iso.ext
  let h := localizationPre_fullyFaithful (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1})
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
  exact h.toHoFullyFaithful.map_preimage _

private lemma postnikovInfinityCone_isLimit_of_nativeHomComparison
    (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (n : ℤ) (hn : 0 ≤ n)
    (e : ∀ A : Mon (Complex R), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingLocalizationFunctor R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovInfinityCone R B n hn) := by
  apply (postnikovInfinityCone_isLimit_iff_cellTests R B n hn).mpr
  intro A
  exact (postnikovCellLocalizationCone_isLimit R A B n hn).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((e A) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso _)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn)).val)

private lemma postnikovInfinityCone_isLimit_of_frameHomComparison
    (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (n : ℤ) (hn : 0 ≤ n)
    (e : ∀ A : Mon (Complex R),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovInfinityCone R B n hn) :=
  postnikovInfinityCone_isLimit_of_nativeHomComparison R B n hn
    (fun A => nativeRepresentableComparison_of_frameComparison R A (e A))

@[expose] public section

/-- 実 AW 降下関手は、指定局所化の元の cell 源からの共変 Hom と全自然同型。 -/
def multiplicativeCellMappingLocalizationHomInfinityIso
    (R : Type u) [CommRing R] (A : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (multiplicativeCellMappingLocalizationFunctor R A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) :=
  localizationFactorizationIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
    (multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫
      nativeCellChosenRightHomInfinityIso R A)

/-- 延長した全同型の前合成は、実 E2 比較の同じ指定二胞体を厳密に回収する。 -/
lemma multiplicativeCellMappingLocalizationHomInfinityIso_precomp
    (R : Type u) [CommRing R] (A : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (multiplicativeCellMappingLocalizationHomInfinityIso R A)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R)) =
        multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫
          nativeCellChosenRightHomInfinityIso R A :=
  nativeRepresentableComparison_precomp R A (nativeCellChosenRightHomInfinityIso R A)

/-- 同じ前合成公式は、選択 frame の中間表示を外した元の AW 比較を回収する。 -/
lemma multiplicativeCellMappingLocalizationHomInfinityIso_precomp_aw
    (R : Type u) [CommRing R] (A : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (multiplicativeCellMappingLocalizationHomInfinityIso R A)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R)) =
        multiplicativeCellMappingLocalizationTriangleIso R A ≪≫
          multiplicativeCellMappingHomInfinityIso R A := by
  rw [multiplicativeCellMappingLocalizationHomInfinityIso_precomp]
  exact Iso.trans_assoc _ _ _

/-- 概要：元の厳密 Postnikov 錐の指定擬同型局所化像は極限錐。
方針：実 AW 全図式比較を元の全錐へ前合成し、実 cell 源の全表現可能試験で検出する。
規約：比較・frame・モデル構造・追加極限性の入力なし。
使われ方：平方零微分摂動による Postnikov 拡大の ∞ 普遍性。 -/
lemma postnikovInfinityCone_isLimit
    (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (n : ℤ) (hn : 0 ≤ n) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovInfinityCone R B n hn) :=
  postnikovInfinityCone_isLimit_of_frameHomComparison R B n hn
    (fun A => nativeCellChosenRightHomInfinityIso R A)

end

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
