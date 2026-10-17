module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtension
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective

/-! # 導来延長の代表加群計算とHom準同型による代表比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既にホモトピー射影的な加群の恒等解像度。 -/
def moduleIdentityProjectiveResolution (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) : ModuleProjectiveResolution A D M where
  obj := M
  π := 𝟙 M
  projective := hM
  quasiIso := fun x => by rw [CategoryTheory.Functor.map_id]; infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元のHomのflatness・有界性なしに代表加群の導来延長を計算する。 -/
def dgDerivedExtensionRepresentableIso (d : D) :
    (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d))) :=
  dgDerivedExtensionResolutionComputation A D E F
      (moduleIdentityProjectiveResolution A D _ (representable_homotopicallyProjective A D d)) ≪≫
    (moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F d)

/-- Hom準同型なら代表加群と制限代表加群の比較は主導来圏で同型。 -/
def representableDerivedRestrictionIso (hF : HomQuasiIso F) (d : D) :
    (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)) ≅
      (moduleToDerived A D).obj ((moduleRestriction A D E F.op).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d)))) :=
  moduleDerivedIso A D (representableRestrictionMap A D E F d)
    (representableRestrictionMap_quasiIso A D E F hF d)

/-- Hom準同型なら、代表加群は導来延長後の導来制限と同型になる。 -/
def dgDerivedRoundTripRepresentableIso (hF : HomQuasiIso F) (d : D) :
    (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)) ≅
      (dgDerivedRestriction A D E F).obj
        ((dgDerivedExtension A D E F).obj
          ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  representableDerivedRestrictionIso A D E F hF d ≪≫
    (eqToIso (congrArg (fun G => G.obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj d))))
      (dgDerivedRestriction_fac A D E F))).symm ≪≫
    (dgDerivedRestriction A D E F).mapIso (dgDerivedExtensionRepresentableIso A D E F d).symm

end SerrePositivity.DifferentialGraded
