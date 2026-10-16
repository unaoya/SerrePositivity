module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleHomotopy
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleResolution
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift

/-! # 導来bimodule圏からK-flat部分圏の局所化への置換関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma rightModuleBimodule_inverse_quasiIso_iff {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        ((rightModuleBimoduleEquivalence A B C).inverse.map f) ↔
      BimoduleCategory.quasiIso A B C f := by
  rw [← rightModuleBimoduleEquivalence_quasiIso_iff]
  let E := rightModuleBimoduleEquivalence A B C
  let W := BimoduleCategory.quasiIso A B C
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) :=
      Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

def bimoduleSourceProjectiveResolution (M : BimoduleCategory A B C) :
    ModuleProjectiveResolution A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence A B C).inverse.obj M) :=
  moduleCanonicalProjectiveResolution A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)

def rightKFlatReplacementMap (hC : localHomKFlat A C) {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    rightKFlatResolutionObj A B C hC M ⟶ rightKFlatResolutionObj A B C hC N :=
  rightKFlatOfModuleMap A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC N).property
    ((bimoduleSourceProjectiveResolution A B C M).lift
      (bimoduleSourceProjectiveResolution A B C N)
      ((rightModuleBimoduleEquivalence A B C).inverse.map f))

lemma rightKFlatReplacementMap_id (hC : localHomKFlat A C) (M : BimoduleCategory A B C) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC (𝟙 M)) =
      𝟙 ((rightKFlatToDerived A B C).obj (rightKFlatResolutionObj A B C hC M)) := by
  have h := (bimoduleSourceProjectiveResolution A B C M).lift_id
  rw [← (rightModuleBimoduleEquivalence A B C).inverse.map_id M] at h
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC M).property
    _ (𝟙 (bimoduleSourceProjectiveResolution A B C M).obj)
    (h.trans ((moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map_id _).symm)
  exact he.trans ((congrArg (rightKFlatToDerived A B C).map
    (rightKFlatOfModuleMap_id A B C _ _)).trans ((rightKFlatToDerived A B C).map_id _))

lemma rightKFlatReplacementMap_comp (hC : localHomKFlat A C)
    {M N P : BimoduleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC (f ≫ g)) =
      (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f) ≫
        (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC g) := by
  let R := bimoduleSourceProjectiveResolution A B C
  let F := (rightModuleBimoduleEquivalence A B C).inverse
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  have h : K.map ((R M).lift (R P) (F.map (f ≫ g))) =
      K.map ((R M).lift (R N) (F.map f) ≫ (R N).lift (R P) (F.map g)) := by
    have he := congrArg (fun k => K.map ((R M).lift (R P) k)) (F.map_comp f g)
    exact he.trans (((R M).lift_comp (R N) (R P) (F.map f) (F.map g)).symm.trans
      (K.map_comp _ _).symm)
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC P).property
    _ _ h
  exact he.trans ((congrArg (rightKFlatToDerived A B C).map
    (rightKFlatOfModuleMap_comp A B C _ (rightKFlatResolutionObj A B C hC N).property _ _ _)).trans
      ((rightKFlatToDerived A B C).map_comp _ _))

def rightKFlatReplacementFunctor (hC : localHomKFlat A C) :
    BimoduleCategory A B C ⥤ DerivedRightKFlatBimoduleCategory A B C where
  obj M := (rightKFlatToDerived A B C).obj (rightKFlatResolutionObj A B C hC M)
  map f := (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)
  map_id := rightKFlatReplacementMap_id A B C hC
  map_comp f g := rightKFlatReplacementMap_comp A B C hC f g

lemma rightKFlatReplacementFunctor_inverts (hC : localHomKFlat A C) :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (rightKFlatReplacementFunctor A B C hC) := by
  intro M N f hf
  apply Localization.inverts (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
  exact (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
    ((bimoduleSourceProjectiveResolution A B C M).lift_quasiIso
      (bimoduleSourceProjectiveResolution A B C N) _
      ((rightModuleBimodule_inverse_quasiIso_iff A B C f).2 hf))

def derivedRightKFlatReplacement (hC : localHomKFlat A C) :
    DerivedBimoduleCategory A B C ⥤ DerivedRightKFlatBimoduleCategory A B C :=
  bimoduleDerivedLift A B C (rightKFlatReplacementFunctor A B C hC)
    (rightKFlatReplacementFunctor_inverts A B C hC)

lemma derivedRightKFlatReplacement_fac (hC : localHomKFlat A C) :
    bimoduleToDerived A B C ⋙ derivedRightKFlatReplacement A B C hC =
      rightKFlatReplacementFunctor A B C hC := bimoduleDerivedLift_fac A B C _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
