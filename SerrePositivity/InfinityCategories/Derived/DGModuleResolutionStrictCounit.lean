module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionSection
/-!
概要：実 dg 分解同値の指定余単位を厳密切断の等式へ同定する。
方針：指定された同じ比較と端点等式を保って全関手射を比較する。
規約：元の指定同型を変更しない。使われ方：実 augmentation と入力比較の正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実分解同値の指定余単位は、同じ厳密切断の等式から得る同型そのものである。 -/
lemma dgModuleFunctorResolutionSourceNerveEquivalence_invHomIso :
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).invHomIso =
      eqToIso (congrArg (fun m => HomotopyCategory.mk (functorVertex m))
        (dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R C E F)) := by
  rfl
end SerrePositivity.InfinityCategories
