module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionProjective
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtension

/-! # graph導来延長と導来制限の射集合の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実際の加群の導来制限の計算同型。 -/
def dgDerivedRestrictionComputation (M : ModuleCategory A E) :
    (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M) ≅
      (moduleToDerived A D).obj ((dgModuleRestriction A D E F.op).onClosed.obj M) :=
  eqToIso (congrArg (fun G => G.obj M) (dgDerivedRestriction_fac A D E F))

/-- 射影的始域に対する、graph導来延長–制限のHom同値。 -/
def dgProjectiveDerivedExtensionHomEquiv (P : ModuleCategory A D)
    (hP : moduleHomotopicallyProjective A D P) (M : ModuleCategory A E) :
    ((moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P) ⟶
        (moduleToDerived A E).obj M) ≃
      ((moduleToDerived A D).obj P ⟶
        (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M)) :=
  (moduleProjectiveDerivedHomEquiv A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) M).symm.trans
    (((dgModuleHomotopyAdjunction A D E F).homEquiv
      ((moduleToHomotopy A D).obj P) ((moduleToHomotopy A E).obj M)).trans
      ((moduleProjectiveDerivedHomEquiv A D hP
        ((dgModuleRestriction A D E F.op).onClosed.obj M)).trans
          (Iso.homCongr (Iso.refl _) (dgDerivedRestrictionComputation A D E F M).symm)))

/-- 指定された実際の加群の導来像に対するHom同値。自然性は別途検証する。 -/
def dgDerivedExtensionHomEquivOnModules (N : ModuleCategory A D) (M : ModuleCategory A E) :
    ((dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj N) ⟶
        (moduleToDerived A E).obj M) ≃
      ((moduleToDerived A D).obj N ⟶
        (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M)) := by
  let P := moduleCanonicalProjectiveResolution A D N
  exact (Iso.homCongr (dgDerivedExtensionResolutionComputation A D E F P) (Iso.refl _)).trans
    ((dgProjectiveDerivedExtensionHomEquiv A D E F P.obj P.projective M).trans
      (Iso.homCongr (moduleDerivedIso A D P.π P.quasiIso) (Iso.refl _)))

/-- 主導来圏の任意の対象の射集合同値。 -/
def dgDerivedExtensionHomEquiv (X : DerivedModuleCategory A D) (Y : DerivedModuleCategory A E) :
    ((dgDerivedExtension A D E F).obj X ⟶ Y) ≃
      (X ⟶ (dgDerivedRestriction A D E F).obj Y) :=
  dgDerivedExtensionHomEquivOnModules A D E F X.as.obj Y.as.obj

end SerrePositivity.DifferentialGraded
