module
public import SerrePositivity.KTheory.G0Supported
public import Mathlib.Algebra.Module.Torsion.Basic

/-! # Classes of modules annihilated by an ideal, over the quotient ring -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] (J : Ideal R)

/-- Convert an annihilator containment into the quotient-action construction's hypothesis. -/
theorem idealAnnihilatorTorsion (M : ModuleCat.{u} R) (h : J ≤ Module.annihilator R M) :
    Module.IsTorsionBySet R M J := fun m r => Module.mem_annihilator.mp (h r.property) m

/-- A finite annihilated module viewed as a finite module over the quotient ring. -/
def annihilatedFGModule (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : J ≤ Module.annihilator R M) :
    SupportedFGModuleOn (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J))) := by
  let hT := idealAnnihilatorTorsion J M h
  letI := hT.module
  have : Module.Finite (R ⧸ J) M := Module.Finite.of_surjective
    hT.semilinearMap Function.surjective_id
  exact ⟨ModuleCat.of (R ⧸ J) M, inferInstance, Set.subset_univ _⟩

/-- The quotient-ring class of a finite annihilated module. -/
def annihilatedClass (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : J ≤ Module.annihilator R M) : G0 (R ⧸ J) := G0WithSupport.mk (annihilatedFGModule J M h)

/-- An R-linear map between annihilated modules is linear over the quotient. -/
def annihilatedLinearMap {M N : ModuleCat.{u} R} [Module.Finite R M] [Module.Finite R N]
    (hM : J ≤ Module.annihilator R M) (hN : J ≤ Module.annihilator R N) (f : M →ₗ[R] N) :
    (annihilatedFGModule J M hM).obj →ₗ[R ⧸ J] (annihilatedFGModule J N hN).obj where
  toFun := f
  map_add' := f.map_add
  map_smul' q m := by
    refine Quotient.inductionOn' q ?_
    intro r
    exact f.map_smul r m

/-- Isomorphic annihilated modules have equal quotient-ring classes. -/
lemma annihilatedClass_iso {M N : ModuleCat.{u} R} [Module.Finite R M] [Module.Finite R N]
    (hM : J ≤ Module.annihilator R M) (hN : J ≤ Module.annihilator R N) (e : M ≅ N) :
    annihilatedClass J M hM = annihilatedClass J N hN := by
  apply G0WithSupport.mk_iso
  exact
    { hom := ModuleCat.ofHom (X := (annihilatedFGModule J M hM).obj)
        (Y := (annihilatedFGModule J N hN).obj) (annihilatedLinearMap J hM hN e.hom.hom)
      inv := ModuleCat.ofHom (X := (annihilatedFGModule J N hN).obj)
        (Y := (annihilatedFGModule J M hM).obj) (annihilatedLinearMap J hN hM e.inv.hom)
      hom_inv_id := by
        ext m
        change e.inv (e.hom m) = m
        exact ConcreteCategory.congr_hom e.hom_inv_id m
      inv_hom_id := by
        ext m
        change e.hom (e.inv m) = m
        exact ConcreteCategory.congr_hom e.inv_hom_id m }

lemma annihilatedClass_of_isZero (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : J ≤ Module.annihilator R M) (hz : IsZero M) : annihilatedClass J M h = 0 := by
  have : Subsingleton (annihilatedFGModule J M h).obj := by
    change Subsingleton M
    exact ModuleCat.subsingleton_of_isZero hz
  exact G0WithSupport.mk_of_subsingleton _

/-- Additivity for short exact sequences whose three modules are annihilated by J. -/
lemma annihilatedClass_shortExact {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (E : SupportedModuleShortExact Z)
    (h₁ : J ≤ Module.annihilator R E.left.obj) (h₂ : J ≤ Module.annihilator R E.middle.obj)
    (h₃ : J ≤ Module.annihilator R E.right.obj) :
    annihilatedClass J E.middle.obj h₂ =
      annihilatedClass J E.left.obj h₁ + annihilatedClass J E.right.obj h₃ := by
  let Q : SupportedModuleShortExact (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J))) :=
    { left := annihilatedFGModule J E.left.obj h₁
      middle := annihilatedFGModule J E.middle.obj h₂
      right := annihilatedFGModule J E.right.obj h₃
      f := annihilatedLinearMap J h₁ h₂ E.f
      g := annihilatedLinearMap J h₂ h₃ E.g
      injective := E.injective
      exact := E.exact
      surjective := E.surjective }
  exact G0WithSupport.mk_shortExact Q
end SerrePositivity
