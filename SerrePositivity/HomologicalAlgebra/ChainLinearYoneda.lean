module
public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.CategoryTheory.Abelian.Ext

/-! # Functorial linear dual cochain complexes of module chain complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The cochain complex Hom(K,-), naturally in the coefficient module. -/
def chainLinearYonedaFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := K.linearYonedaObj R M
  map f :=
    { f := fun i => ModuleCat.ofHom (Linear.rightComp R (K.X i) f)
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        ext g
        rfl }
  map_id M := by
    ext i g
    rfl
  map_comp f g := by
    ext i h
    rfl

/-- Unoppositing a chain map commutes with its cohomology comparison. -/
lemma chainHomologyUnop_hom_naturality
    {K L : ChainComplex (ModuleCat.{u} R)ᵒᵖ ℕ} (f : K ⟶ L) (i : ℕ) :
    homologyMap ((unopFunctor (ModuleCat R) (.down ℕ)).map f.op) i ≫
        (homologyUnop K i).hom =
      (homologyUnop L i).hom ≫ (homologyMap f i).unop := by
  let ψ := (unopFunctor (ModuleCat R) (.down ℕ)).map f.op
  have h := congrArg Quiver.Hom.unop (homologyOp_hom_naturality ψ i)
  change (homologyUnop L i).hom ≫ (homologyMap f i).unop =
    homologyMap ψ i ≫ (homologyUnop K i).hom at h
  exact h.symm

/-- The inverse unop homology comparison is natural as well. -/
lemma chainHomologyUnop_inv_naturality
    {K L : ChainComplex (ModuleCat.{u} R)ᵒᵖ ℕ} (f : K ⟶ L) (i : ℕ) :
    (homologyMap f i).unop ≫ (homologyUnop K i).inv =
      (homologyUnop L i).inv ≫
        homologyMap ((unopFunctor (ModuleCat R) (.down ℕ)).map f.op) i := by
  apply (cancel_epi (homologyUnop L i).hom).mp
  rw [← Category.assoc, ← chainHomologyUnop_hom_naturality f i]
  simp

/-- Precomposition by a chain map gives a natural morphism of dual cochain functors. -/
def chainLinearYonedaMap {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) :
    chainLinearYonedaFunctor L ⟶ chainLinearYonedaFunctor K where
  app M :=
    { f := fun i => ModuleCat.ofHom (Linear.leftComp R M (f.f i))
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        ext g
        change (K.d j i ≫ f.f i) ≫ g = (f.f j ≫ L.d j i) ≫ g
        rw [f.comm] }
  naturality {M N} g := by
    ext i h
    rfl

@[simp] lemma chainLinearYonedaMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    chainLinearYonedaMap (𝟙 K) = 𝟙 (chainLinearYonedaFunctor K) := by
  ext M i g
  rfl

lemma chainLinearYonedaMap_comp {K L P : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ P) :
    chainLinearYonedaMap (f ≫ g) = chainLinearYonedaMap g ≫ chainLinearYonedaMap f := by
  ext M i h
  rfl

end SerrePositivity
