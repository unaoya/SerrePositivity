module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenFrameCoherent
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseAscent
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.InvertingFunctorIsoInvariance

/-!
概要：実 cell 写像の全標的図式を、指定した dg 擬同型局所化上へ降ろす。
方針：既存の局所化の宇宙上昇と反転関手の因子化を、元の実図式へ適用する。
規約：比較二胞体を保持する。表現可能 Hom との同定はここでは主張しない。
使われ方：E2-S (6) の指定局所化比較と、元の Postnikov 錐の像の接続。
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

def multiplicativeCellMappingLocalizationFunctor :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (quasiIsoInfinity R) ⟶ SpaceInfinity.{u + 1} :=
  localizationDescend
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
    (multiplicativeCellMappingInfinityCoherent R A)
    (multiplicativeCellMappingInfinityCoherent_inverts R A)

def multiplicativeCellMappingLocalizationTriangleIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        multiplicativeCellMappingLocalizationFunctor R A)
      (multiplicativeCellMappingInfinityCoherent R A) :=
  localizationDescendIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
    (multiplicativeCellMappingInfinityCoherent R A)
    (multiplicativeCellMappingInfinityCoherent_inverts R A)

def multiplicativeCellMappingLocalizationChosenTriangleIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        multiplicativeCellMappingLocalizationFunctor R A)
      (kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A)) :=
  multiplicativeCellMappingLocalizationTriangleIso R A ≪≫
    multiplicativeCellMappingChosenRightCoherentIso R A

lemma nativeCellChosenRightInfinityCoherent_inverts :
    InvertsEdges (kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R) :=
  ((multiplicativeCellMappingChosenRightCoherentIso R A).invertsEdges_iff _).mp
    (multiplicativeCellMappingInfinityCoherent_inverts R A)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
