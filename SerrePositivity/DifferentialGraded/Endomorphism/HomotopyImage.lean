module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectImage

/-! # 加群値dg関手の主Kにおけるthick閉包の像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

def dgModuleFunctorHomotopyImageComputation (M : ModuleCategory A D) :
    F.onHomotopy.obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToHomotopy A B).obj (F.onClosed.obj M) := Iso.refl _

def dgModuleFunctorHomotopyShiftIso (s : ℤ) (X : ModuleHomotopyCategory A D) :
    F.onHomotopy.obj (X⟦s⟧) ≅ (F.onHomotopy.obj X)⟦s⟧ :=
  F.onHomotopy.mapIso (((moduleToHomotopy A D).commShiftIso s).app X.as).symm ≪≫
    dgModuleFunctorHomotopyImageComputation A D B F (X.as⟦s⟧) ≪≫
    (moduleToHomotopy A B).mapIso
      (dgModuleFunctorShiftIso A B D F s (ForgetEnrichment.to (Complex A) X.as)) ≪≫
    ((moduleToHomotopy A B).commShiftIso s).app (F.onClosed.obj X.as) ≪≫
    (shiftFunctor (ModuleHomotopyCategory A B) s).mapIso
      (dgModuleFunctorHomotopyImageComputation A D B F X.as).symm

/-- dg像は指定対象の有限thick閉包を、像を含む任意のthick部分圏へ送る。 -/
lemma dgModuleFunctor_thick_image (E : RightModule A D)
    (P : ObjectProperty (ModuleHomotopyCategory A B)) [P.IsTriangulated]
    [P.IsStableUnderRetracts]
    (hE : P (F.onHomotopy.obj ((moduleToHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) E)))) :
    ∀ X, endomorphismThickClosure A D E X → P (F.onHomotopy.obj X) := by
  intro X hX
  induction hX with
  | generator => exact hE
  | zero => exact P.prop_of_isZero (F.onHomotopy.map_isZero (Limits.isZero_zero _))
  | shift s _ ih =>
      exact P.prop_of_iso (dgModuleFunctorHomotopyShiftIso A D B F s _).symm
        (P.le_shift s _ ih)
  | triangle T hT _ _ ih₁ ih₂ =>
      obtain ⟨M, N, f, ⟨e⟩⟩ := hT
      have hM := P.prop_of_iso
        (F.onHomotopy.mapIso (Triangle.π₁.mapIso e) ≪≫
          dgModuleFunctorHomotopyImageComputation A D B F M) ih₁
      have hN := P.prop_of_iso
        (F.onHomotopy.mapIso (Triangle.π₂.mapIso e) ≪≫
          dgModuleFunctorHomotopyImageComputation A D B F N) ih₂
      have hc := P.ext_of_isTriangulatedClosed₃'
        (moduleHomotopyConeTriangle A B (F.onClosed.map f))
        (moduleHomotopyConeTriangle_distinguished A B (F.onClosed.map f)) hM hN
      rw [ObjectProperty.isoClosure_eq_self] at hc
      exact P.prop_of_iso
        ((moduleToHomotopy A B).mapIso (dgModuleFunctorConeIso A D B F f) ≪≫
          (dgModuleFunctorHomotopyImageComputation A D B F (moduleCone A D f)).symm ≪≫
          F.onHomotopy.mapIso (Triangle.π₃.mapIso e.symm)) hc
  | retract a _ ih => exact P.prop_of_retract (a.map F.onHomotopy) ih

end SerrePositivity.DifferentialGraded
