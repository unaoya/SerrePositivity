module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-! # dg関手に沿う右dg加群の導来制限

制限は対象ごとに評価するため任意の準同型を保ち、置換を要さず主局所化へ降りる。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- opposite上の指定dg関手に沿う導来制限。 -/
def moduleDerivedRestriction (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedLift A E (moduleRestriction A D E F ⋙ moduleToDerived A D) (by
    intro M N f hf
    exact moduleToDerived_inverts A D _ (moduleRestriction_quasiIso A D E F f hf))

lemma moduleDerivedRestriction_fac (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    moduleToDerived A E ⋙ moduleDerivedRestriction A D E F =
      moduleRestriction A D E F ⋙ moduleToDerived A D := moduleDerivedLift_fac _ _ _ _

/-- 通常向きのdg関手からoppositeを構成して制限する入口。 -/
def dgDerivedRestriction (F : DGFunctor A D E) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedRestriction A D E F.op

lemma dgDerivedRestriction_fac (F : DGFunctor A D E) :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      moduleRestriction A D E F.op ⋙ moduleToDerived A D :=
  moduleDerivedRestriction_fac A D E F.op

end SerrePositivity.DifferentialGraded
