module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementShift

/-! # 受入済みの主Perf係数変更の整合的shift・三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectDerivedTransportIso (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)) ≅ perfectScalarDerivedExtension φ D S :=
  Functor.isoWhiskerLeft (perfectDGModuleHomotopyEquivalence A D S).inverse
      (scalarPerfectHomotopyComparison φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).counitIso
      (perfectScalarDerivedExtension φ D S) ≪≫
    (perfectScalarDerivedExtension φ D S).leftUnitor

local instance (S : Set D) : (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  scalarPerfectHomotopyExtensionCommShift φ D S

@[instance_reducible]
def perfectScalarDerivedExtensionCommShift (S : Set D) :
    (perfectScalarDerivedExtension φ D S).CommShift ℤ :=
  Functor.CommShift.ofIso (scalarPerfectDerivedTransportIso φ D S) ℤ

lemma scalarPerfectDerivedTransportIso_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectDerivedTransportIso φ D S).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (scalarPerfectDerivedTransportIso φ D S) ℤ

lemma perfectScalarDerivedExtensionIsTriangulated (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    (perfectScalarDerivedExtension φ D S).IsTriangulated := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectDerivedTransportIso_commShift φ D S
  let := scalarPerfectHomotopyExtensionIsTriangulated φ D S
  have : ((perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
      (scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S))).IsTriangulated := inferInstance
  exact Functor.isTriangulated_of_iso (scalarPerfectDerivedTransportIso φ D S)

/-- U13同値の単位を用いて正規化した主Perfの係数変更正方形。 -/
def scalarPerfectHomotopyShiftComparison (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectScalarDerivedExtension φ D S ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) :=
  Functor.isoWhiskerLeft (perfectDGModuleToPerfect A D S)
      (scalarPerfectDerivedTransportIso φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).unitIso.symm _ ≪≫
    Functor.leftUnitor _

lemma scalarPerfectHomotopyShiftComparison_eq (S : Set D) :
    scalarPerfectHomotopyShiftComparison φ D S = scalarPerfectHomotopyComparison φ D S := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  dsimp [scalarPerfectHomotopyShiftComparison, scalarPerfectDerivedTransportIso]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  let e := perfectDGModuleHomotopyEquivalence A D S
  let G := perfectScalarDerivedExtension φ D S
  let H := scalarPerfectHomotopyExtension φ D S ⋙
    perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let α : e.functor ⋙ G ≅ H := scalarPerfectHomotopyComparison φ D S
  change G.map (e.counitIso.inv.app (e.functor.obj X)) ≫
    α.hom.app (e.inverse.obj (e.functor.obj X)) ≫ H.map (e.unitIso.inv.app X) = α.hom.app X
  rw [← α.hom.naturality, Functor.comp_map, ← Category.assoc, ← G.map_comp,
    e.counitInv_functor_comp]
  exact (congrArg (fun k => k ≫ α.hom.app X) (G.map_id (e.functor.obj X))).trans
    (Category.id_comp _)

lemma scalarPerfectHomotopyShiftComparison_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyShiftComparison φ D S).hom ℤ := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectDerivedTransportIso_commShift φ D S
  unfold scalarPerfectHomotopyShiftComparison
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

lemma scalarPerfectHomotopyComparison_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyComparison φ D S).hom ℤ := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  rw [← scalarPerfectHomotopyShiftComparison_eq φ D S]
  exact scalarPerfectHomotopyShiftComparison_commShift φ D S

def scalarPerfectHomotopyTriangleSquareIso (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    (perfectDGModuleToPerfect A D S).mapTriangle ⋙
        (perfectScalarDerivedExtension φ D S).mapTriangle ≅
      (scalarPerfectHomotopyExtension φ D S).mapTriangle ⋙
        (perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).mapTriangle := by
  letI := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectHomotopyComparison_commShift φ D S
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (scalarPerfectHomotopyComparison φ D S) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
