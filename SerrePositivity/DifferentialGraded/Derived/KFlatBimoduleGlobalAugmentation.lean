module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleAugmentation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComparison

/-! # 全導来bimodule圏におけるK-flat置換増大射の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [Small.{u} C] in
lemma rightKFlatDerivedInclusion_map_base {M N : RightKFlatBimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatDerivedInclusion A B C).map ((rightKFlatToDerived A B C).map f) =
      (bimoduleToDerived A B C).map f.hom :=
  eq_of_heq (Functor.hcongr_hom (rightKFlatDerivedInclusion_fac A B C) f)

lemma rightKFlatGlobalAugmentation_naturality (hC : localHomKFlat A C)
    {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatDerivedInclusion A B C).map ((rightKFlatReplacementFunctor A B C hC).map f) ≫
        (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C N).π =
      (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C M).π ≫
        (bimoduleToDerived A B C).map f := by
  change (rightKFlatDerivedInclusion A B C).map
    ((rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)) ≫ _ = _
  rw [rightKFlatDerivedInclusion_map_base]
  let H := rightModuleBimoduleEquivalence A B C
  let R := bimoduleSourceProjectiveResolution A B C
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  have hs : K.map ((R M).lift (R N) (H.inverse.map f) ≫ (R N).π) =
      K.map ((R M).π ≫ H.inverse.map f) :=
    (K.map_comp _ _).trans (((R M).lift_fac (R N) (H.inverse.map f)).trans (K.map_comp _ _).symm)
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy _ _ hs
  have hl : H.functor.map ((R M).lift (R N) (H.inverse.map f) ≫ (R N).π) ≫
        (H.counitIso.app N).hom =
      (rightKFlatReplacementMap A B C hC f).hom ≫
        (bimoduleCanonicalSemifreeResolution A B C N).π := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app N).hom =
      H.functor.map _ ≫ (H.functor.map (R N).π ≫ (H.counitIso.app N).hom)
    rw [H.functor.map_comp, Category.assoc]
  have hr : H.functor.map ((R M).π ≫ H.inverse.map f) ≫ (H.counitIso.app N).hom =
      (bimoduleCanonicalSemifreeResolution A B C M).π ≫ f := by
    change H.functor.map ((R M).π ≫ H.inverse.map f) ≫ (H.counitIso.app N).hom =
      (H.functor.map (R M).π ≫ (H.counitIso.app M).hom) ≫ f
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map (R M).π ≫ k) (H.counitIso.hom.naturality f)
  have hh := congrArg (fun k => k ≫ (bimoduleToDerived A B C).map (H.counitIso.app N).hom) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp, hr] at hh
  exact ((bimoduleToDerived A B C).map_comp _ _).symm.trans
    (hh.trans ((bimoduleToDerived A B C).map_comp _ _))

def rightKFlatGlobalAugmentationIso (hC : localHomKFlat A C) :
    rightKFlatReplacementFunctor A B C hC ⋙ rightKFlatDerivedInclusion A B C ≅
      bimoduleToDerived A B C :=
  NatIso.ofComponents
    (fun M => bimoduleDerivedIso A B C (bimoduleCanonicalSemifreeResolution A B C M).π
      (bimoduleCanonicalSemifreeResolution A B C M).quasiIso)
    (fun f => rightKFlatGlobalAugmentation_naturality A B C hC f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
