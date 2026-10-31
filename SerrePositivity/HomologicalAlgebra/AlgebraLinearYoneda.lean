module
public import SerrePositivity.HomologicalAlgebra.LinearYoneda
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Linear dual cochain complexes over the actual coefficient algebra -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {α : Type*} [AddRightCancelSemigroup α] [One α]

/-- Precomposition is linear over the coefficient algebra, without linearity of all R-modules. -/
def algebraLinearYonedaPrecomp {P Q : ModuleCat.{u} R} (f : P ⟶ Q) (M : ModuleCat.{u} C) :
    (Q ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) →ₗ[C]
      (P ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) where
  toFun g := f ≫ g
  map_add' g h := by simp only [Preadditive.comp_add]
  map_smul' c g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Hom_R(K,M) is an actual cochain complex of C-modules for every C-module M. -/
def algebraLinearYonedaObj (K : ChainComplex (ModuleCat.{u} R) α) (M : ModuleCat.{u} C) :
    CochainComplex (ModuleCat.{u} C) α where
  X i := ModuleCat.of C (K.X i ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M)
  d i j := ModuleCat.ofHom (algebraLinearYonedaPrecomp (K.d j i) M)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change K.d j i ≫ g = 0
    rw [K.shape _ _ hij, zero_comp]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change K.d k j ≫ K.d j i ≫ g = 0
    rw [← Category.assoc, K.d_comp_d, zero_comp]

/-- Coefficient C-linear maps induce C-linear postcomposition on each dual term. -/
def algebraLinearYonedaPostcomp (P : ModuleCat.{u} R)
    {M N : ModuleCat.{u} C} (f : M ⟶ N) :
    (P ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) →ₗ[C]
      (P ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj N) where
  toFun g := g ≫ (ModuleCat.restrictScalars (algebraMap R C)).map f
  map_add' g h := by simp only [Preadditive.add_comp]
  map_smul' c g := by
    apply ModuleCat.hom_ext
    ext x
    exact f.hom.map_smul c (g x)

/-- Actual C-linear dual complexes depend functorially on their C-module coefficients. -/
def algebraLinearYonedaFunctor (K : ChainComplex (ModuleCat.{u} R) α) :
    ModuleCat.{u} C ⥤ CochainComplex (ModuleCat.{u} C) α where
  obj M := algebraLinearYonedaObj K M
  map f :=
    { f := fun i => ModuleCat.ofHom (algebraLinearYonedaPostcomp (K.X i) f)
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        change K.d j i ≫ (g ≫ (ModuleCat.restrictScalars (algebraMap R C)).map f) =
          (K.d j i ≫ g) ≫ (ModuleCat.restrictScalars (algebraMap R C)).map f
        exact (Category.assoc _ _ _).symm }
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change g ≫ 𝟙 _ = g
    exact Category.comp_id g
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x ≫ ((ModuleCat.restrictScalars (algebraMap R C)).map f ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map g) =
      (x ≫ (ModuleCat.restrictScalars (algebraMap R C)).map f) ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map g
    exact (Category.assoc _ _ _).symm

/-- Forgetting the coefficient algebra gives exactly the original R-linear dual complex. -/
def algebraLinearYonedaRestrictIso (K : ChainComplex (ModuleCat.{u} R) α)
    (M : ModuleCat.{u} C) :
    ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up α)).obj
        ((algebraLinearYonedaFunctor (C := C) K).obj M) ≅
      (chainLinearYonedaFunctor K).obj ((ModuleCat.restrictScalars (algebraMap R C)).obj M) :=
  Iso.refl _

/-- The coefficient restriction comparison is natural in all C-linear coefficient maps. -/
def algebraLinearYonedaRestrictNatIso (K : ChainComplex (ModuleCat.{u} R) α) :
    algebraLinearYonedaFunctor (C := C) K ⋙
        (ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up α) ≅
      ModuleCat.restrictScalars (algebraMap R C) ⋙ chainLinearYonedaFunctor K :=
  NatIso.ofComponents (algebraLinearYonedaRestrictIso K) (by
    intro M N f
    ext i g
    rfl)

/-- Chain maps act contravariantly by C-linear precomposition on actual coefficient duals. -/
def algebraLinearYonedaMap {K L : ChainComplex (ModuleCat.{u} R) α} (f : K ⟶ L) :
    algebraLinearYonedaFunctor (C := C) L ⟶ algebraLinearYonedaFunctor (C := C) K where
  app M :=
    { f := fun i => ModuleCat.ofHom (algebraLinearYonedaPrecomp (f.f i) M)
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        change (K.d j i ≫ f.f i) ≫ g = (f.f j ≫ L.d j i) ≫ g
        rw [f.comm] }
  naturality {M N} g := by
    ext i h
    rfl

/-- Precomposition by the identity is the identity on C-linear dual complexes. -/
@[simp] lemma algebraLinearYonedaMap_id (K : ChainComplex (ModuleCat.{u} R) α) :
    algebraLinearYonedaMap (C := C) (𝟙 K) = 𝟙 (algebraLinearYonedaFunctor (C := C) K) := by
  ext M i g
  rfl

/-- Precomposition reverses the order of composition, with its actual coefficient structure. -/
lemma algebraLinearYonedaMap_comp {K L P : ChainComplex (ModuleCat.{u} R) α}
    (f : K ⟶ L) (g : L ⟶ P) :
    algebraLinearYonedaMap (C := C) (f ≫ g) =
      algebraLinearYonedaMap (C := C) g ≫ algebraLinearYonedaMap (C := C) f := by
  ext M i h
  rfl

/-- Restriction also respects the maps induced by chain maps, including Koszul transitions. -/
lemma algebraLinearYonedaRestrictNatIso_chain_map
    {K L : ChainComplex (ModuleCat.{u} R) α} (f : K ⟶ L) :
    Functor.whiskerRight (algebraLinearYonedaMap (C := C) f)
        ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up α)) ≫
        (algebraLinearYonedaRestrictNatIso (C := C) K).hom =
      (algebraLinearYonedaRestrictNatIso (C := C) L).hom ≫
        Functor.whiskerLeft (ModuleCat.restrictScalars (algebraMap R C))
          (chainLinearYonedaMap f) := by
  ext M i g
  rfl

/-- Postcomposition respects scalar multiplication by the actual coefficient algebra. -/
lemma algebraLinearYonedaFunctor_map_smul (K : ChainComplex (ModuleCat.{u} R) α)
    {M N : ModuleCat.{u} C} (c : C) (f : M ⟶ N) :
    (algebraLinearYonedaFunctor (C := C) K).map (c • f) =
      c • (algebraLinearYonedaFunctor (C := C) K).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The coefficient-dual functor is additive by actual postcomposition. -/
instance algebraLinearYonedaFunctor_additive (K : ChainComplex (ModuleCat.{u} R) α) :
    (algebraLinearYonedaFunctor (C := C) K).Additive where
  map_add {X Y f g} := by
    ext i h
    rfl

/-- The verified coefficient action makes the dual functor C-linear. -/
instance algebraLinearYonedaFunctor_linear (K : ChainComplex (ModuleCat.{u} R) α) :
    Functor.Linear C (algebraLinearYonedaFunctor (C := C) K) where
  map_smul f c := algebraLinearYonedaFunctor_map_smul K c f

end SerrePositivity
