module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaPinchedInput

/-! 実 cochain 持ち上げを前合成した鎖入力の二端・primitive を射影へ照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open CartesianMonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  {T : Type (max u v)} [DGCategory R T] {x' y' : T}
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hp : g ≫ q = f ≫ q)
  (hz : h.comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hp hz in
lemma dgGluingCochainIdentityCommaLift_projection_input {P : Complex R} (t : P ⟶ K) :
    let φ := t ≫ dgGluingCochainIdentityCommaLift R E x y K f g h he
    (φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q =
      φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q) ∧
    (((Cochain.ofHom φ).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) = 0) := by
  dsimp only
  let φ := t ≫ dgGluingCochainIdentityCommaLift R E x y K f g h he
  have hsrc : φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) =
      t ≫ g := by
    dsimp only [φ]
    rw [Category.assoc, dgGluingIdentityCommaTarget_map,
      dgGluingCochainIdentityCommaLift_end]
  have hrep : φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) =
      t ≫ f := by
    change (t ≫ dgGluingCochainIdentityCommaLift R E x y K f g h he) ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
    rw [Category.assoc, dgGluingCochainIdentityCommaLift_start]
  have hpair : φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q =
      φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q := by
    rw [← Category.assoc, hsrc, ← Category.assoc φ, hrep, Category.assoc,
      Category.assoc, hp]
  have hprim : ((Cochain.ofHom φ).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) = 0 := by
    dsimp only [φ]
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom t)
      (Cochain.ofHom (dgGluingCochainIdentityCommaLift R E x y K f g h he))
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _),
      dgGluingCochainIdentityCommaLift_primitive,
      Cochain.comp_assoc_of_first_is_zero_cochain, Cochain.neg_comp, hz,
      neg_zero, Cochain.comp_zero]
  exact ⟨hpair, hprim⟩

end SerrePositivity.InfinityCategories
