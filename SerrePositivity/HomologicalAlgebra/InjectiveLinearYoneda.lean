module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYoneda
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Exact linear duality for injective coefficient modules -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The module-valued linear Yoneda functor preserves limits. -/
instance linearYonedaModule_preservesLimits (J : ModuleCat.{u} R) :
    PreservesLimits ((linearYoneda R (ModuleCat.{u} R)).obj J) := by
  have : PreservesLimits (((linearYoneda R (ModuleCat.{u} R)).obj J) ⋙
      forget (ModuleCat.{u} R)) := by
    change PreservesLimits (yoneda.obj J)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Injective coefficients make linear duality preserve epimorphisms as well. -/
instance linearYonedaModule_preservesEpimorphisms (J : ModuleCat.{u} R) [Injective J] :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesEpimorphisms := by
  let : (yoneda.obj J).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_yoneda_obj J).mp inferInstance
  have : (((linearYoneda R (ModuleCat.{u} R)).obj J) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms := by
    change (yoneda.obj J).PreservesEpimorphisms
    infer_instance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    ((linearYoneda R (ModuleCat.{u} R)).obj J) (forget (ModuleCat.{u} R))

/-- Linear duality with injective coefficients preserves actual homology. -/
instance linearYonedaModule_preservesHomology (J : ModuleCat.{u} R) [Injective J] :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The defined dual cochain complex is the linear Yoneda image of the opposite chain complex. -/
def chainLinearYonedaObjIsoMapOp (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (J : ModuleCat.{u} R) :
    K.linearYonedaObj R J ≅
      ((((linearYoneda R (ModuleCat.{u} R)).obj J).mapHomologicalComplex (.up ℕ)).obj K.op) :=
  Iso.refl _

/-- Injective coefficients identify dual cohomology with the actual linear dual of homology. -/
def injectiveChainLinearYonedaHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) :
    (K.linearYonedaObj R J).homology i ≅ ModuleCat.of R (K.homology i ⟶ J) :=
  (K.op.sc i).mapHomologyIso ((linearYoneda R (ModuleCat.{u} R)).obj J) ≪≫
    ((linearYoneda R (ModuleCat.{u} R)).obj J).mapIso (homologyOp K i)

/-- This duality respects the actual dual chain map, including its contravariant direction. -/
lemma injectiveChainLinearYonedaHomologyIso_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) :
    homologyMap ((chainLinearYonedaMap f).app J) i ≫
        (injectiveChainLinearYonedaHomologyIso K J i).hom =
      (injectiveChainLinearYonedaHomologyIso L J i).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj J).map (homologyMap f i).op := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  let ψ := (opFunctor (ModuleCat.{u} R) (.down ℕ)).map f.op
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{u} R)ᵒᵖ (.up ℕ) i).map ψ) F
  change homologyMap ((chainLinearYonedaMap f).app J) i ≫
      ((K.op.sc i).mapHomologyIso F).hom =
    ((L.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyMap ψ i) at h
  change _ ≫ (((K.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyOp K i).hom) =
    (((L.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyOp L i).hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp,
    homologyOp_hom_naturality, F.map_comp, Category.assoc]

/-- Zero original homology maps yield zero dual cohomology maps for injective coefficients. -/
lemma chainLinearYonedaMap_homology_eq_zero_of_injective
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hf : homologyMap f i = 0) :
    homologyMap ((chainLinearYonedaMap f).app J) i = 0 := by
  apply (cancel_mono (injectiveChainLinearYonedaHomologyIso K J i).hom).mp
  rw [zero_comp, injectiveChainLinearYonedaHomologyIso_naturality, hf]
  simp only [op_zero, linearYoneda_obj_map, unop_zero, Preadditive.IsIso.comp_left_eq_zero]
  ext g x
  change g (0 : L.homology i) = 0
  exact (g : L.homology i ⟶ J).hom.map_zero

end SerrePositivity
