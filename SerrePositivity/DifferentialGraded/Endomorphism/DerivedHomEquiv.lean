module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensor
public import SerrePositivity.DifferentialGraded.Endomorphism.TensorProjective

/-! # 再構成導来tensorと導来Homの射集合の比較

射影解像度、主Kの随伴、射影的始域の局所化Hom計算を組み合わせる。
ここでの射集合同値の両変数自然性は、導来随伴を組み立てる際の別証明義務。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

/-- 実際の加群の主導来像における導来Homの計算。 -/
def endomorphismDerivedHomComputation (M : ModuleCategory A D) :
    (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A (EndomorphismObject E)).obj
        ((endomorphismModuleHom A D E).onClosed.obj M) :=
  eqToIso (congrArg (fun F => F.obj M) (endomorphismDerivedHom_fac A D E hE))

/-- 射影的右End(E)加群を始域とする、導来圏のHomの実際の同値。 -/
def endomorphismProjectiveDerivedHomEquiv
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P) (M : ModuleCategory A D) :
    ((moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P) ⟶
        (moduleToDerived A D).obj M) ≃
      ((moduleToDerived A (EndomorphismObject E)).obj P ⟶
        (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M)) :=
  (moduleProjectiveDerivedHomEquiv A D
      (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) M).symm.trans
    (((endomorphismHomotopyAdjunction A D E).homEquiv
      ((moduleToHomotopy A (EndomorphismObject E)).obj P) ((moduleToHomotopy A D).obj M)).trans
      ((moduleProjectiveDerivedHomEquiv A (EndomorphismObject E) hP
        ((endomorphismModuleHom A D E).onClosed.obj M)).trans
          (Iso.homCongr (Iso.refl _) (endomorphismDerivedHomComputation A D E hE M).symm)))

/-- 任意の右End(E)加群と右D加群の主導来像におけるtensor–Hom同値。 -/
def endomorphismDerivedTensorHomEquivOnModules
    (N : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D) :
    ((endomorphismDerivedTensor A D E).obj ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶
        (moduleToDerived A D).obj M) ≃
      ((moduleToDerived A (EndomorphismObject E)).obj N ⟶
        (endomorphismDerivedHom A D E hE).obj ((moduleToDerived A D).obj M)) := by
  let P := moduleCanonicalProjectiveResolution A (EndomorphismObject E) N
  exact (Iso.homCongr (endomorphismDerivedTensorResolutionComputation A D E P) (Iso.refl _)).trans
    ((endomorphismProjectiveDerivedHomEquiv A D E hE P.obj P.projective M).trans
      (Iso.homCongr (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso) (Iso.refl _)))

/-- 主導来圏の任意の対象についてのtensor–Hom射集合同値。 -/
def endomorphismDerivedTensorHomEquiv
    (X : DerivedModuleCategory A (EndomorphismObject E)) (Y : DerivedModuleCategory A D) :
    ((endomorphismDerivedTensor A D E).obj X ⟶ Y) ≃
      (X ⟶ (endomorphismDerivedHom A D E hE).obj Y) :=
  endomorphismDerivedTensorHomEquivOnModules A D E hE X.as.obj Y.as.obj

end SerrePositivity.DifferentialGraded
