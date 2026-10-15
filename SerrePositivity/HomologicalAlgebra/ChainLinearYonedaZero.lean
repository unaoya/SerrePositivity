module
public import SerrePositivity.HomologicalAlgebra.InjectiveLinearYoneda

/-! # Degree-zero dual cohomology without injectivity assumptions -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- At the initial cochain degree, linear duality preserves homology for all coefficients. -/
lemma chainLinearYoneda_preserves_zero_leftHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (J : ModuleCat.{u} R) :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesLeftHomologyOf (K.op.sc 0) := by
  apply Functor.preservesLeftHomology_of_zero_f
  change K.op.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply K.op.shape
  change ¬ ((ComplexShape.up ℕ).prev 0 + 1 = 0)
  omega

/-- The same boundary condition also preserves right homology data at degree zero. -/
lemma chainLinearYoneda_preserves_zero_rightHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (J : ModuleCat.{u} R) :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesRightHomologyOf (K.op.sc 0) := by
  apply Functor.preservesRightHomology_of_zero_f
  change K.op.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply K.op.shape
  change ¬ ((ComplexShape.up ℕ).prev 0 + 1 = 0)
  omega

/-- Degree-zero cohomology of the dual is Hom from degree-zero homology, for any coefficients. -/
def chainLinearYonedaZeroHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (J : ModuleCat.{u} R) :
    (K.linearYonedaObj R J).homology 0 ≅ ModuleCat.of R (K.homology 0 ⟶ J) := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  letI : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  exact (K.op.sc 0).mapHomologyIso F ≪≫ F.mapIso (homologyOp K 0)

/-- The zero-degree comparison is natural in chain maps without injective coefficients. -/
lemma chainLinearYonedaZeroHomologyIso_chain_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (J : ModuleCat.{u} R) :
    homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
        (chainLinearYonedaZeroHomologyIso K J).hom =
      (chainLinearYonedaZeroHomologyIso L J).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj J).map (homologyMap f 0).op := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  have : F.PreservesLeftHomologyOf (L.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology L J
  let : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let : ((L.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let ψ := (opFunctor (ModuleCat.{u} R) (.down ℕ)).map f.op
  have h := ShortComplex.mapHomologyIso_hom_naturality
    (S₁ := L.op.sc 0) (S₂ := K.op.sc 0)
    ((shortComplexFunctor (ModuleCat.{u} R)ᵒᵖ (.up ℕ) 0).map ψ) F
  change homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
      ((K.op.sc 0).mapHomologyIso F).hom =
    ((L.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyMap ψ 0) at h
  change _ ≫ (((K.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp K 0).hom) =
    (((L.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp L 0).hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp,
    homologyOp_hom_naturality, F.map_comp, Category.assoc]

/-- The zero-degree comparison is also natural in arbitrary coefficient morphisms. -/
lemma chainLinearYonedaZeroHomologyIso_coefficient_naturality
    (K : ChainComplex (ModuleCat.{u} R) ℕ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    homologyMap ((chainLinearYonedaFunctor K).map f) 0 ≫
        (chainLinearYonedaZeroHomologyIso K J').hom =
      (chainLinearYonedaZeroHomologyIso K J).hom ≫
        ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.homology 0))).map f := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  let G := (linearYoneda R (ModuleCat.{u} R)).obj J'
  let τ : F ⟶ G := (linearYoneda R (ModuleCat.{u} R)).map f
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  have : G.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J'
  let : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let : ((K.op.sc 0).map G).HasHomology := CategoryWithHomology.hasHomology _
  have : F.PreservesRightHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_rightHomology K J
  have : G.PreservesRightHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_rightHomology K J'
  have h := ShortComplex.homologyMap_mapNatTrans (K.op.sc 0) τ
  change homologyMap ((chainLinearYonedaFunctor K).map f) 0 =
    ((K.op.sc 0).mapHomologyIso F).hom ≫ τ.app (K.op.homology 0) ≫
      ((K.op.sc 0).mapHomologyIso G).inv at h
  change _ ≫ (((K.op.sc 0).mapHomologyIso G).hom ≫ G.map (homologyOp K 0).hom) =
    (((K.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp K 0).hom) ≫
      τ.app (op (K.homology 0))
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← τ.naturality]

/-- Zero dual cohomology is the represented Hom functor, naturally in all coefficients. -/
def chainLinearYonedaZeroHomologyNatIso (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    chainLinearYonedaFunctor K ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.homology 0)) :=
  NatIso.ofComponents (fun J => chainLinearYonedaZeroHomologyIso K J)
    (fun f => chainLinearYonedaZeroHomologyIso_coefficient_naturality K f)

end SerrePositivity
