module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedFreeCone
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
/-!
概要：一段 cone 表示のラベル型に、全 Hom を保持する dg 圏と固定関手作用を与える。
方針：実 cone 評価から Hom 複体を引き戻し、同じ延長比較を一般共役入口へ渡す。
規約：反復閉性・関手変数の厳密法則・native core の作用は別に検証する。
使われ方：16時間試作で cone 係数を持つ小さい表示の全次数作用を確認する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

instance dgKappaPresentedFreeConeEnrichment :
    DGCategory R (DGKappaPresentedFreeConeObject R D κ) :=
  inducedDGCategory R
    (fun X => ForgetEnrichment.to (Complex R) (dgKappaPresentedFreeConeValue R D κ X))

def dgKappaPresentedFreeConeEvaluation :
    DGFunctor R (DGKappaPresentedFreeConeObject R D κ) (RightModule R D) :=
  inducedDGEvaluation R
    (fun X => ForgetEnrichment.to (Complex R) (dgKappaPresentedFreeConeValue R D κ X))

variable (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def dgKappaPresentedFreeConeAction :
    DGFunctor R (DGKappaPresentedFreeConeObject R D κ) (DGKappaPresentedFreeConeObject R E κ) :=
  inducedDGFunctorClosedConjugate R
    (fun X => ForgetEnrichment.to (Complex R) (dgKappaPresentedFreeConeValue R D κ X))
    (fun X => ForgetEnrichment.to (Complex R) (dgKappaPresentedFreeConeValue R E κ X))
    (dgModuleExtension R D E F) (dgKappaPresentedFreeConeObjectMap R D κ E F)
    (fun X => by
      unfold dgKappaPresentedFreeConeValue dgKappaPresentedFreeConeObjectMap
        dgKappaPresentedFreeArrowMap
      exact dgKappaPresentedFreeConeExtensionIso R D κ E F X)

end SerrePositivity.InfinityCategories
