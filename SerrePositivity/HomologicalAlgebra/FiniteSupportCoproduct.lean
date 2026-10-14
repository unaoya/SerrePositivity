module
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-! # Finite generation of coproducts with finitely many nonzero summands -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R]

/-- A finite categorical coproduct of finite modules is a finite module. -/
lemma moduleFinite_finite_coproduct {ι : Type} [Finite ι] (F : ι → ModuleCat.{u} R)
    [∀ i, Module.Finite R (F i)] : Module.Finite R (∐ F : ModuleCat.{u} R) := by
  classical
  let e := (ModuleCat.coprodIsoDirectSum F).toLinearEquiv
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- A possibly infinite coproduct is finite when only a finite set of summands is nonzero. -/
lemma moduleFinite_coproduct_of_finiteSupport {ι : Type} (F : ι → ModuleCat.{u} R)
    [∀ i, Module.Finite R (F i)] (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (F i)) :
    Module.Finite R (∐ F : ModuleCat.{u} R) := by
  classical
  let G : {i // i ∈ s} → ModuleCat.{u} R := fun i => F i.val
  have : Module.Finite R (∐ G : ModuleCat.{u} R) := moduleFinite_finite_coproduct G
  let f : ∐ G ⟶ ∐ F := Sigma.desc (fun i => Sigma.ι F i.val)
  let U := LinearMap.range f.hom
  let q : ∐ F ⟶ ModuleCat.of R ((∐ F : ModuleCat.{u} R) ⧸ U) := ModuleCat.ofHom U.mkQ
  have hfg : f ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero U).mpr ⟨x, rfl⟩
  have hq : q = 0 := by
    apply Sigma.hom_ext
    intro i
    by_cases hi : i ∈ s
    · have h := congrArg (fun k => Sigma.ι G ⟨i, hi⟩ ≫ k) hfg
      simpa only [Category.assoc, f, Sigma.ι_comp_desc_assoc, comp_zero] using h
    · exact (hs i hi).eq_of_src _ _
  have hq' : U.mkQ = 0 := congrArg ModuleCat.Hom.hom hq
  have hu : U = ⊤ := by rw [← Submodule.ker_mkQ U, hq', LinearMap.ker_zero]
  exact Module.Finite.of_surjective f.hom (LinearMap.range_eq_top.mp hu)

/-- Projective summands give a projective coproduct, also for small index types. -/
lemma projective_coproduct_of_projective {ι : Type} (F : ι → ModuleCat.{u} R)
    (hp : ∀ i, Projective (F i)) : Projective (∐ F) where
  factors f e he := by
    have := he
    let g := fun i => by
      have := hp i
      exact Projective.factorThru (Sigma.ι F i ≫ f) e
    refine ⟨Sigma.desc g, ?_⟩
    apply Sigma.hom_ext
    intro i
    dsimp [g]
    simp

/-- Remove zero summands outside a finite support from a categorical coproduct. -/
def coproductFiniteSupportIso {ι : Type} (F : ι → ModuleCat.{u} R)
    (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (F i)) :
    (∐ F : ModuleCat.{u} R) ≅ ∐ (fun i : {i // i ∈ s} => F i.val) := by
  classical
  let G := fun i : {i // i ∈ s} => F i.val
  let f : (∐ F : ModuleCat.{u} R) ⟶ ∐ G :=
    Sigma.desc (fun i => if h : i ∈ s then Sigma.ι G ⟨i, h⟩ else 0)
  let g : (∐ G : ModuleCat.{u} R) ⟶ ∐ F := Sigma.desc (fun i => Sigma.ι F i.val)
  refine ⟨f, g, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    by_cases hi : i ∈ s
    · simp [f, g, G, hi]
    · exact (hs i hi).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp [f, g, G, i.property]
end SerrePositivity
