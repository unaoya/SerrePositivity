module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameCoherent
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPresentedMappingCone
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の Postnikov 提示錐上で、AW と実始域 frame の全錐比較を保持する。
方針：全標的の実関手同型を、元の錐の join 全体に前合成する。
規約：指定局所化後の極限性も、strict coherent 錐との比較も仮定しない。
使われ方：E2-S (6) と P-8 を元の頂点・脚・全錐へ適用する接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovPresentedCellFrameConeIso :
    FunctorIso
      ((JoinCone.ulift.{u + 1, u + 2}
        (F1B.nerveCone (postnikovInfinityPresentedCone R B n hn))).val ≫
          multiplicativeCellMappingInfinityCoherent R A)
      ((JoinCone.ulift.{u + 1, u + 2}
        (F1B.nerveCone (postnikovInfinityPresentedCone R B n hn))).val ≫
          kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A)) :=
  FunctorIso.precomp (multiplicativeCellMappingSourceFrameCoherentIso R A)
    (JoinCone.ulift.{u + 1, u + 2}
      (F1B.nerveCone (postnikovInfinityPresentedCone R B n hn))).val

lemma postnikovPresentedCellFrameCone_isLimit_iff :
    IsLimitCone (mapJoinCone (multiplicativeCellMappingInfinityCoherent R A)
      (JoinCone.ulift.{u + 1, u + 2}
        (F1B.nerveCone (postnikovInfinityPresentedCone R B n hn)))) ↔
      IsLimitCone (mapJoinCone
        (kanDiagramCoherentNerve (nativeCellSourceFrameInfinityKanFunctor R A))
        (JoinCone.ulift.{u + 1, u + 2}
          (F1B.nerveCone (postnikovInfinityPresentedCone R B n hn)))) := by
  constructor
  · intro hc
    exact hc.of_functorIso (postnikovPresentedCellFrameConeIso R A B n hn)
  · intro hc
    exact hc.of_functorIso (postnikovPresentedCellFrameConeIso R A B n hn).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
