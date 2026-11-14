module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-!
概要：境界付き cone 降下の後合成を実 augmentation の零境界降下と照合する。
方針：同じ次数別成分と原始元の零像を使って厳密な等式を示す。
規約：ホモトピー類への移行はしない。使われ方：canonical cell 段の strict lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleConeBoundaryDesc_postcompose_zero
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {L M T N : ModuleCategory R D} (a : L ⟶ M)
    (h : (moduleHom R D (ForgetEnrichment.to (Complex R) L)
      (ForgetEnrichment.to (Complex R) T)).X (-1)) (b : M ⟶ T)
    (hh : (moduleHom R D (ForgetEnrichment.to (Complex R) L)
      (ForgetEnrichment.to (Complex R) T)).d (-1) 0 h =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (C := RightModule R D) (X := L) (Y := T) (a ≫ b))).val)
    (q : T ⟶ N) (hq : (eHomWhiskerLeft (Complex R) L q).f (-1) h = 0)
    (f : M ⟶ N) (hb : b ≫ q = f) (ha : a ≫ f = 0) :
    moduleConeDescOfBoundary R D a h b hh ≫ q = moduleConeDesc R D a f ha := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeDescOfBoundary_eval, moduleConeDesc_eval]
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, mappingCone.desc_f _ _ _ _ p (p + 1) rfl,
    complexConeDesc_f]
  have hpost := congrArg
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) L)
      (ForgetEnrichment.to (Complex R) N) x).f (-1)) hq
  rw [moduleHomWhiskerLeft_apply_π, map_zero] at hpost
  have hv := Cochain.congr_v hpost (p + 1) p (by omega)
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v] at hv
  have hbf := congrArg (fun c => ((moduleEvaluation R D x).map c).f p) hb
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at hbf
  rw [Preadditive.add_comp, Category.assoc, hv, comp_zero, zero_add, Category.assoc, hbf]
lemma dgModuleConeDesc_postcompose
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {L M T N : ModuleCategory R D} (a : L ⟶ M) (b : M ⟶ T) (ha : a ≫ b = 0)
    (q : T ⟶ N) :
    moduleConeDesc R D a b ha ≫ q =
      moduleConeDesc R D a (b ≫ q) (by rw [← Category.assoc, ha, zero_comp]) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeDesc_eval, moduleConeDesc_eval]
  apply HomologicalComplex.Hom.ext
  funext p
  simp only [HomologicalComplex.comp_f, complexConeDesc_f,
    CategoryTheory.Functor.map_comp, Category.assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
