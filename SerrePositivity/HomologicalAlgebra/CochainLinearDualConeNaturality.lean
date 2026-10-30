module
public import SerrePositivity.HomologicalAlgebra.LinearYoneda
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

/-! # Naturality of the signed dual cone comparison in its coefficient module -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Cone maps act by the given left map on the first product component. -/
lemma mappingConeTermProdIso_map_fst (φ : K ⟶ L) (ψ : K' ⟶ L')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso ψ q).hom
        ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q x)).1 =
      α.left.f (q + 1) ((mappingConeTermProdIso φ q).hom x).1 := by
  have h := DerivedCompletion.moduleConeArrowMap_fst φ ψ α q (q + 1) rfl
  rw [← mappingConeTermProdIso_fst ψ q, ← mappingConeTermProdIso_fst φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Cone maps act by the given right map on the second product component. -/
lemma mappingConeTermProdIso_map_snd (φ : K ⟶ L) (ψ : K' ⟶ L')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso ψ q).hom
        ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q x)).2 =
      α.right.f q ((mappingConeTermProdIso φ q).hom x).2 := by
  have h := DerivedCompletion.moduleConeArrowMap_snd φ ψ α q
  rw [← mappingConeTermProdIso_snd ψ q, ← mappingConeTermProdIso_snd φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Coefficient functoriality gives a square between the actual reversed dual maps. -/
abbrev cochainLinearDualConeCoefficientArrow (φ : K ⟶ L)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Arrow.mk ((cochainLinearDualMap φ).app M) ⟶ Arrow.mk ((cochainLinearDualMap φ).app N) :=
  Arrow.homMk ((cochainLinearDualFunctor L).map f) ((cochainLinearDualFunctor K).map f)
    ((cochainLinearDualMap φ).naturality f)

/-- The standard cone map induced by a coefficient morphism. -/
abbrev cochainLinearDualConeCoefficientMap (φ : K ⟶ L)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    CochainComplex.mappingCone ((cochainLinearDualMap φ).app M) ⟶
      CochainComplex.mappingCone ((cochainLinearDualMap φ).app N) :=
  mapArrowHom _ _ (fun k => ⟨k - 1, by simp⟩) (cochainLinearDualConeCoefficientArrow φ f)

/-- The shifted signed comparison is natural for arbitrary coefficient morphisms. -/
lemma cochainLinearDualConeShiftIso_naturality (φ : K ⟶ L)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f)⟦(1 : ℤ)⟧' ≫
        (cochainLinearDualConeShiftIso φ N).hom =
      (cochainLinearDualConeShiftIso φ M).hom ≫ cochainLinearDualConeCoefficientMap φ f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply (cancel_mono (mappingConeTermProdIso ((cochainLinearDualMap φ).app N) i).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (mappingConeTermProdIso ((cochainLinearDualMap φ).app N) i).hom
      ((cochainLinearDualConeShiftTermIso φ N i).hom
        (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f).f (i + 1) x)) =
    (mappingConeTermProdIso ((cochainLinearDualMap φ).app N) i).hom
      ((cochainLinearDualConeCoefficientMap φ f).f i
        ((cochainLinearDualConeShiftTermIso φ M i).hom x))
  apply Prod.ext
  · erw [mappingConeTermProdIso_map_fst, cochainLinearDualConeShiftTermIso_fst,
      cochainLinearDualConeShiftTermIso_fst]
    change inrX φ (0 - (i + 1)) ≫ (x ≫ f) = (inrX φ (0 - (i + 1)) ≫ x) ≫ f
    exact (Category.assoc _ _ _).symm
  · erw [mappingConeTermProdIso_map_snd, cochainLinearDualConeShiftTermIso_snd,
      cochainLinearDualConeShiftTermIso_snd]
    change -(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫
        (x ≫ f)) =
      (-(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫ x)) ≫ f
    simp only [Preadditive.neg_comp, Category.assoc]

/-- Removing the shift preserves naturality of the actual dual cone comparison. -/
lemma cochainLinearDualConeIso_naturality (φ : K ⟶ L)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f ≫
        (cochainLinearDualConeIso φ N).hom =
      (cochainLinearDualConeIso φ M).hom ≫
        (cochainLinearDualConeCoefficientMap φ f)⟦(-1 : ℤ)⟧' := by
  let U := shiftFunctorCompIsoId (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ) (-1) (by omega)
  have h := congrArg ((shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)).map)
    (cochainLinearDualConeShiftIso_naturality φ f)
  simp only [Functor.map_comp] at h
  change (cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f ≫ U.inv.app _ ≫
      (cochainLinearDualConeShiftIso φ N).hom⟦(-1 : ℤ)⟧' =
    (U.inv.app _ ≫ (cochainLinearDualConeShiftIso φ M).hom⟦(-1 : ℤ)⟧') ≫
      (cochainLinearDualConeCoefficientMap φ f)⟦(-1 : ℤ)⟧'
  have hU := U.inv.naturality
    ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f)
  change (cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f ≫ U.inv.app _ =
    U.inv.app _ ≫
      (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).map f)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' at hU
  rw [← Category.assoc]
  erw [hU]
  simpa only [Category.assoc] using congrArg (fun g => U.inv.app _ ≫ g) h

/-- Transporting the two arrows preserves their standard cone map. -/
lemma mappingConeArrowMap_eqToHom (φ ψ : K ⟶ L) (φ' ψ' : K' ⟶ L')
    (h : φ = ψ) (h' : φ' = ψ') (α : Arrow.mk φ ⟶ Arrow.mk φ')
    (β : Arrow.mk ψ ⟶ Arrow.mk ψ') (hl : α.left = β.left) (hr : α.right = β.right) :
    mapArrowHom φ φ' (fun k => ⟨k - 1, by simp⟩) α ≫
        eqToHom (congrArg (fun t : K' ⟶ L' => CochainComplex.mappingCone t) h') =
      eqToHom (congrArg (fun t : K ⟶ L => CochainComplex.mappingCone t) h) ≫
        mapArrowHom ψ ψ' (fun k => ⟨k - 1, by simp⟩) β := by
  subst ψ
  subst ψ'
  have he : α = β := Arrow.hom_ext _ _ hl hr
  subst β
  simp

end SerrePositivity
