module
public import SerrePositivity.InfinityCategories.Derived.DGKappaSeedExtensionBase
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveClosureExtensionRange
/-!
概要：全ての κ-small seed の実 dg 延長を、標的の同じ閉代表族でホモトピー同型まで被覆する。
方針：sphere-free／perfect の基底を検査し、零・shift・直和・cone の超限帰納法へ渡す。
規約：精密化した閉射の標的射との一致は別に要求し、延長の充満性を仮定しない。
使われ方：c′ ゲート3の異なる出発コードを共通コードへ送る seed の代表化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CategoryTheory.Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

include hκ hreg in
lemma dgKappaClosedProjectiveSeed_extension_homotopyRange
    (i : (dgKappaClosedProjectiveFamily R C κ).1) :
    dgModuleHomotopyRange R D (dgKappaClosedProjectiveObjects R D κ)
      ((dgModuleExtension R C D F).onClosed.obj
        (((dgKappaClosedProjectiveFamily R C κ).2 i).val)) := by
  letI : PreservesColimitsOfSize.{u, u} (dgModuleExtension R C D F).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R C D F).leftAdjoint_preservesColimits
  exact dgProjectiveClosureStage_extension_homotopyRange R C D
    (dgModuleExtension R C D F) (dgKappaClosedProjectiveObjects R D κ)
    (dgKappaClosedProjectiveObjects_zero R D hκ)
    (dgKappaClosedProjectiveObjects_shift R D hκ hreg)
    (dgKappaClosedProjectiveObjects_binaryClosed R D hκ hreg)
    (dgKappaClosedProjectiveObjects_cone R D hκ hreg)
    (dgKappaClosedProjectiveObjects_countableClosed R D hκ hreg)
    (dgKappaClosedProjectiveBaseFamily R C κ)
    (dgKappaClosedProjectiveBase_extension_homotopyRange R C D F κ hκ) i.1 i.2

end SerrePositivity.InfinityCategories
