module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMappingDescentLimit
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellTestCriterion
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness

/-!
概要：実 cell 写像関手の表現可能比較を、元の Postnikov 錐の判定へ代入する私有組立て。
方針：全標的 FunctorIso を元の錐全体へ前合成し、実試験錐の極限性を輸送する。
規約：比較の存在は未供給で、主経路の代替となる公開条件付き定理は置かない。
使われ方：E2-S (6) の実比較を受領した際の適用箇所。
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
    (e : FunctorIso (kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    FunctorIso (multiplicativeCellMappingLocalizationFunctor R A)
      (homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A))) :=
  localizationFactorizationIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
    (multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫ e)

private lemma nativeRepresentableComparison_precomp
    (R : Type u) [CommRing R] (A : Mon (Complex R))
    (e : FunctorIso (kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
        homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    FunctorIso.precomp (nativeRepresentableComparison_of_frameComparison R A e)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R)) =
        multiplicativeCellMappingLocalizationChosenTriangleIso R A ≪≫ e := by
  apply Iso.ext
  let h := localizationPre_fullyFaithful (Y := SpaceInfinity.{u + 1})
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R))
    (ULift.up.{u + 2, u + 1} '' quasiIsoInfinityEdges R)
    (IsLocalization.ulift.{u + 1, u + 2} (quasiIsoInfinity_isLocalization R))
  exact h.toHoFullyFaithful.map_preimage _

private lemma postnikovInfinityCone_isLimit_of_nativeHomComparison
    (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (n : ℤ) (hn : 0 ≤ n)
    (e : ∀ A : Mon (Complex R), FunctorIso (multiplicativeCellMappingLocalizationFunctor R A)
      (homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    IsLimitCone (postnikovInfinityCone R B n hn) := by
  apply (postnikovInfinityCone_isLimit_iff_cellTests R B n hn).mpr
  intro A
  exact (postnikovCellLocalizationCone_isLimit R A B n hn).of_functorIso
    (FunctorIso.precomp ((e A) ≪≫ F2.Compact.homInfinityCovariant_covariantIso _)
      (JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn)).val)

private lemma postnikovInfinityCone_isLimit_of_frameHomComparison
    (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (n : ℤ) (hn : 0 ≤ n)
    (e : ∀ A : Mon (Complex R),
      FunctorIso (kanDiagramCoherentNerve (nativeCellChosenRightInfinityKanFunctor R A))
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (quasiIsoInfinityMap R) ≫
          homInfinityCovariant (quasiIsoInfinityVertex R (cellResolution R A)))) :
    IsLimitCone (postnikovInfinityCone R B n hn) :=
  postnikovInfinityCone_isLimit_of_nativeHomComparison R B n hn
    (fun A => nativeRepresentableComparison_of_frameComparison R A (e A))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
