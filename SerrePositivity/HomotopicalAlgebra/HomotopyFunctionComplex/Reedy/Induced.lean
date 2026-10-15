module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import Mathlib.CategoryTheory.InducedCategory

/-! # Reedy structures on injectively indexed induced categories

An injective indexing of objects whose image is closed under inverse maps
inherits the actual unique Reedy factorizations. This permits an explicit
old-object/new-object presentation of a truncated Reedy category.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {K : Type w} (e : K → J)
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)

abbrev inducedInverse := inverse.inverseImage (inducedFunctor e)
abbrev inducedDirect := direct.inverseImage (inducedFunctor e)

lemma identities_endpoints {x y : J} (f : x ⟶ y)
    (hf : MorphismProperty.identities J f) : x = y := by
  cases hf
  rfl

lemma identities_eqToHom {x y : J} (f : x ⟶ y)
    (hf : MorphismProperty.identities J f) : f = eqToHom (identities_endpoints f hf) := by
  cases hf
  rfl

omit [inverse.IsMultiplicative] [direct.IsMultiplicative] in
lemma induced_identities (he : Function.Injective e) {x y : InducedCategory J e}
    (f : x ⟶ y) (hf : MorphismProperty.identities J f.hom) :
    MorphismProperty.identities (InducedCategory J e) f := by
  have hxy : e x = e y := identities_endpoints f.hom hf
  have hxy' : x = y := he hxy
  subst y
  have h : f.hom = 𝟙 (e x) := identities_eqToHom f.hom hf
  have : f = 𝟙 x := InducedCategory.hom_ext h
  subst f
  exact MorphismProperty.ofHoms.mk _

abbrev inducedForgetFactorization {x y : InducedCategory J e} {f : x ⟶ y}
    (q : MorphismProperty.MapFactorizationData
      (inducedInverse (inverse := inverse) e) (inducedDirect (direct := direct) e) f) :
    MorphismProperty.MapFactorizationData inverse direct f.hom where
  Z := e q.Z
  i := q.i.hom
  p := q.p.hom
  fac := congrArg (fun f ↦ f.hom) q.fac
  hi := q.hi
  hp := q.hp

omit [inverse.IsMultiplicative] [direct.IsMultiplicative] in
lemma inducedForgetFactorization_injective (he : Function.Injective e)
    {x y : InducedCategory J e} (f : x ⟶ y) :
    Function.Injective
      (inducedForgetFactorization (inverse := inverse) (direct := direct) e (f := f)) := by
  rintro ⟨Z, ⟨i⟩, ⟨p⟩, h, hi, hp⟩ ⟨Z', ⟨i'⟩, ⟨p'⟩, h', hi', hp'⟩ hq
  have hZ : e Z = e Z' := congrArg (fun q ↦ q.Z) hq
  have hZ' := he hZ
  subst Z'
  change (MorphismProperty.MapFactorizationData.mk (e Z) i p _ hi hp) =
    (MorphismProperty.MapFactorizationData.mk (e Z) i' p' _ hi' hp') at hq
  cases hq
  rfl

variable (he : Function.Injective e)
  (hclosed : ∀ (x : K) {y : J} (f : e x ⟶ y), inverse f → ∃ z, e z = y)

def inducedFactorization {x y : InducedCategory J e} (f : x ⟶ y) :
    MorphismProperty.MapFactorizationData
      (inducedInverse (inverse := inverse) e) (inducedDirect (direct := direct) e) f := by
  have h : Nonempty (MorphismProperty.MapFactorizationData
      (inducedInverse (inverse := inverse) e) (inducedDirect (direct := direct) e) f) := by
    rcases r.mapFactorizationData f.hom with ⟨Z, i, p, hfac, hi, hp⟩
    obtain ⟨z, hz⟩ := hclosed x i hi
    cases hz
    exact ⟨{
      Z := z
      i := InducedCategory.homMk i
      p := InducedCategory.homMk p
      fac := InducedCategory.hom_ext hfac
      hi := hi
      hp := hp }⟩
  exact h.some

def inducedReedy : ReedyStructure
    (inducedInverse (inverse := inverse) e) (inducedDirect (direct := direct) e) α where
  deg x := r.deg (e x)
  lt₁ f hf hf' := r.lt₁ f.hom hf (fun h ↦ hf' (induced_identities e he f h))
  lt₂ f hf hf' := r.lt₂ f.hom hf (fun h ↦ hf' (induced_identities e he f h))
  nonempty_unique f := by
    have := r.subsingleton_mapFactorizationData f.hom
    have : Subsingleton (MorphismProperty.MapFactorizationData
        (inducedInverse (inverse := inverse) e) (inducedDirect (direct := direct) e) f) :=
      (inducedForgetFactorization_injective e he f).subsingleton
    exact ⟨{
      default := inducedFactorization e r hclosed f
      uniq := fun _ ↦ Subsingleton.elim _ _ }⟩

end SerrePositivity.Reedy
