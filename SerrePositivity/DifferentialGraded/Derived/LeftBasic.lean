module
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-! # 左dg加群の指定準同型局所化 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群閉零圏のobjectwise quasiIsoによる構成された局所化。 -/
abbrev DerivedLeftModuleCategory := (leftModuleQuasiIso A D).Localization

/-- 左加群の指定局所化関手。 -/
abbrev leftModuleToDerived : LeftModuleCategory A D ⥤ DerivedLeftModuleCategory A D :=
  (leftModuleQuasiIso A D).Q

lemma leftModuleToDerived_inverts :
    (leftModuleQuasiIso A D).IsInvertedBy (leftModuleToDerived A D) :=
  Localization.inverts _ _

/-- 指定された左準同型の像の同型。 -/
def leftModuleDerivedIso {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    (leftModuleToDerived A D).obj L ≅ (leftModuleToDerived A D).obj L' :=
  Localization.Construction.wIso (W := leftModuleQuasiIso A D) g hg

end SerrePositivity.DifferentialGraded
