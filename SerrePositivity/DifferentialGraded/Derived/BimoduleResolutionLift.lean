module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleGlobalAugmentation

/-! # 標準bimodule解像度から任意の準同型への持ち上げ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 標的は射影的でなくてよい。持ち上げの三角形は全dg自然なホモトピーまで可換。 -/
def bimoduleCanonicalResolutionSourceLift {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleSourceProjectiveResolution A B C M).obj ⟶
      (rightModuleBimoduleEquivalence A B C).inverse.obj N :=
  Classical.choose (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (bimoduleSourceProjectiveResolution A B C M).projective
    ((rightModuleBimoduleEquivalence A B C).inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A B C q).2 hq)
    (bimoduleSourceProjectiveResolution A B C M).π)

def bimoduleCanonicalResolutionLift {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleCanonicalSemifreeResolution A B C M).obj ⟶ N :=
  (rightModuleBimoduleEquivalence A B C).functor.map
      (bimoduleCanonicalResolutionSourceLift A B C q hq) ≫
    ((rightModuleBimoduleEquivalence A B C).counitIso.app N).hom

lemma bimoduleCanonicalResolutionLift_fac {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleToDerived A B C).map (bimoduleCanonicalResolutionLift A B C q hq) ≫
        (bimoduleToDerived A B C).map q =
      (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C M).π := by
  let H := rightModuleBimoduleEquivalence A B C
  let P := bimoduleSourceProjectiveResolution A B C M
  have hs := Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ P.projective (H.inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A B C q).2 hq) P.π)
  have hsK : (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map
      (bimoduleCanonicalResolutionSourceLift A B C q hq ≫ H.inverse.map q) =
        (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map P.π :=
    (moduleToHomotopy_map_eq_iff A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _ _).2 hs
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy _ _ hsK
  have hl : H.functor.map
        (bimoduleCanonicalResolutionSourceLift A B C q hq ≫ H.inverse.map q) ≫
        (H.counitIso.app M).hom = bimoduleCanonicalResolutionLift A B C q hq ≫ q := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app M).hom =
      (H.functor.map _ ≫ (H.counitIso.app N).hom) ≫ q
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map
      (bimoduleCanonicalResolutionSourceLift A B C q hq) ≫ k) (H.counitIso.hom.naturality q)
  have hh := congrArg (fun k => k ≫ (bimoduleToDerived A B C).map
    (H.counitIso.app M).hom) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp] at hh
  exact ((bimoduleToDerived A B C).map_comp _ _).symm.trans hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
