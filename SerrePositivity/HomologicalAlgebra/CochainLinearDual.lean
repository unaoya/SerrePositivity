module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYoneda
public import SerrePositivity.HomologicalAlgebra.Resolution

/-! # Integer-indexed linear dual cochain complexes and their nonnegative restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Reversing integer degrees converts a cochain complex to a chain complex. -/
def integerNegEmbedding : ComplexShape.Embedding (.down ℤ) (.up ℤ) :=
  .mk' _ _ (fun i => 0 - i) (fun _ _ h => by dsimp at h; omega) (by dsimp; omega)

instance integerNegEmbedding_isRelIff : integerNegEmbedding.IsRelIff := by
  dsimp [integerNegEmbedding]
  infer_instance

/-- The nonnegative degrees, embedded without changing their integer value. -/
def nonnegativeCochainEmbedding : ComplexShape.Embedding (.up ℕ) (.up ℤ) :=
  .mk' _ _ (fun n => (n : ℤ)) (fun _ _ h => by dsimp at h; omega) (by dsimp; omega)

instance nonnegativeCochainEmbedding_isRelIff : nonnegativeCochainEmbedding.IsRelIff := by
  dsimp [nonnegativeCochainEmbedding]
  infer_instance

/-- The dual cochain complex has Hom(K^(-i),M) in integer degree i. -/
abbrev cochainLinearDualFunctor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  chainLinearYonedaFunctor (K.restriction integerNegEmbedding)

/-- A complex map induces contravariant precomposition on its integer-indexed dual. -/
abbrev cochainLinearDualMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    cochainLinearDualFunctor L ⟶ cochainLinearDualFunctor K :=
  chainLinearYonedaMap (restrictionMap f integerNegEmbedding)

/-- Restricting the integer dual recovers the actual nonnegative dual used for Ext. -/
def cochainLinearDualNonnegativeIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) :
    ((cochainLinearDualFunctor K).obj M).restriction nonnegativeCochainEmbedding ≅
      (chainLinearYonedaFunctor (toChain K)).obj M :=
  Iso.refl _

/-- The restriction comparison is natural in every coefficient map. -/
def cochainLinearDualNonnegativeNatIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainLinearDualFunctor K ⋙ nonnegativeCochainEmbedding.restrictionFunctor (ModuleCat R) ≅
      chainLinearYonedaFunctor (toChain K) :=
  NatIso.ofComponents (cochainLinearDualNonnegativeIso K) (fun _ => rfl)

/-- The comparison also respects contravariant maps of the original complexes. -/
lemma cochainLinearDualNonnegativeNatIso_complex_map
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    Functor.whiskerRight (cochainLinearDualMap f)
        (nonnegativeCochainEmbedding.restrictionFunctor (ModuleCat R)) ≫
        (cochainLinearDualNonnegativeNatIso K).hom =
      (cochainLinearDualNonnegativeNatIso L).hom ≫
        chainLinearYonedaMap (restrictionMap f embUp) := by
  apply NatTrans.ext
  funext M
  ext i g
  rfl

/-- The actual dual term, identified with categorical linear morphisms from the reversed term. -/
def cochainLinearDualTermIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (i : ℤ) :
    ((cochainLinearDualFunctor K).obj M).X i ≅ ModuleCat.of R (K.X (0 - i) ⟶ M) :=
  Iso.refl _

/-- The differential of the dual is actual precomposition, with no hidden sign convention. -/
lemma cochainLinearDual_d_apply (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (i j : ℤ) (f : K.X (0 - i) ⟶ M) :
    (((cochainLinearDualFunctor K).obj M).d i j).hom f = K.d (0 - j) (0 - i) ≫ f := rfl

/-- Coefficient morphisms act by postcomposition on every integer dual term. -/
lemma cochainLinearDual_map_apply (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ℤ) (g : K.X (0 - i) ⟶ M) :
    (((cochainLinearDualFunctor K).map f).f i).hom g = g ≫ f := rfl

end SerrePositivity
