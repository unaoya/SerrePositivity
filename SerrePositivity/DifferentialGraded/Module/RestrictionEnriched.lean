module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # dg関手に沿う制限のHom複体上の構成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- 任意パラメータの全次数自然変換をdg関手に沿って引き戻す。 -/
def moduleRestrictionParam {K : Complex A} {M N : RightModule A E}
    (τ : GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj K)
      (restrictModule A D E F M).toFunctor (restrictModule A D E F N).toFunctor where
  app x := τ.app (F.obj x)
  naturality x y := by
    change (β_ K (x ⟶[Complex A] y)).hom ≫
      ((F.map x y ≫ M.map (F.obj x) (F.obj y)) ⊗ₘ τ.app (F.obj y)) ≫
        enrichedComposition _ _ _ =
      (τ.app (F.obj x) ⊗ₘ (F.map x y ≫ N.map (F.obj x) (F.obj y))) ≫
        enrichedComposition _ _ _
    have h := congrArg (fun t => (𝟙 K ⊗ₘ F.map x y) ≫ t)
      (τ.naturality (F.obj x) (F.obj y))
    change (𝟙 K ⊗ₘ F.map x y) ≫ (β_ K _).hom ≫
      (M.map (F.obj x) (F.obj y) ⊗ₘ τ.app (F.obj y)) ≫ enrichedComposition _ _ _ =
      (𝟙 K ⊗ₘ F.map x y) ≫ (τ.app (F.obj x) ⊗ₘ N.map (F.obj x) (F.obj y)) ≫
        enrichedComposition _ _ _ at h
    rw [BraidedCategory.braiding_naturality_assoc] at h
    simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

variable [Small.{u} D] [Small.{u} E]

/-- 主Hom endから制限後の主Hom endへのchain map。 -/
def moduleRestrictionHom (M N : RightModule A E) :
    moduleHom A E M N ⟶ moduleHom A D (restrictModule A D E F M)
      (restrictModule A D E F N) :=
  (moduleHomEquiv A D _ _ _).symm
    (moduleRestrictionParam A D E F ((moduleHomEquiv A E _ M N) (𝟙 _)))

@[reassoc] lemma moduleRestrictionHom_π (M N : RightModule A E) (d : D) :
    moduleRestrictionHom A D E F M N ≫ moduleHomπ A D _ _ d =
      moduleHomπ A E M N (F.obj (op d)).unop := by
  rw [moduleRestrictionHom, moduleHomEquiv_symm_π]
  change 𝟙 _ ≫ moduleHomπ A E M N (F.obj (op d)).unop = _
  exact Category.id_comp _

lemma moduleRestrictionHom_identity (M : RightModule A E) :
    moduleIdentity A E M ≫ moduleRestrictionHom A D E F M M =
      moduleIdentity A D (restrictModule A D E F M) := by
  apply moduleHom_ext
  intro d
  rw [Category.assoc, moduleRestrictionHom_π, moduleIdentity_π, moduleIdentity_π]
  rfl

lemma moduleRestrictionHom_comp (M N P : RightModule A E) :
    moduleComposition A E M N P ≫ moduleRestrictionHom A D E F M P =
      (moduleRestrictionHom A D E F M N ⊗ₘ moduleRestrictionHom A D E F N P) ≫
        moduleComposition A D (restrictModule A D E F M) (restrictModule A D E F N)
          (restrictModule A D E F P) := by
  apply moduleHom_ext
  intro d
  simp only [Category.assoc, moduleRestrictionHom_π, moduleComposition_π]
  rw [tensorHom_comp_tensorHom_assoc, moduleRestrictionHom_π, moduleRestrictionHom_π]
  rfl

/-- 前合成による全次数Hom上のdg制限関手。 -/
def dgModuleRestriction : DGFunctor A (RightModule A E) (RightModule A D) where
  obj M := restrictModule A D E F M
  map M N := moduleRestrictionHom A D E F M N
  map_id := moduleRestrictionHom_identity A D E F
  map_comp := moduleRestrictionHom_comp A D E F

lemma dgModuleRestriction_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map ((dgModuleRestriction A D E F).onClosed.map f) =
      (moduleEvaluation A E (F.obj (op d)).unop).map f := by
  apply CochainComplex.HomComplex.Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, moduleEvaluation_cochain]
  change (moduleHomπ A D _ _ d).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      moduleRestrictionHom A D E F _ _)).val = _
  rw [cycleFromUnit_postcomp]
  exact congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
    (moduleRestrictionHom_π A D E F (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) d)

lemma dgModuleRestriction_map {M N : ModuleCategory A E} (f : M ⟶ N) :
    (dgModuleRestriction A D E F).onClosed.map f = (moduleRestriction A D E F).map f := by
  apply moduleMorphism_ext
  intro d
  rw [dgModuleRestriction_map_eval, moduleRestriction_map_eval]

lemma dgModuleRestriction_onClosed_eq :
    (dgModuleRestriction A D E F).onClosed = moduleRestriction A D E F := by
  apply CategoryTheory.Functor.ext
  swap
  · intro M
    rfl
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact dgModuleRestriction_map A D E F f

end SerrePositivity.DifferentialGraded
