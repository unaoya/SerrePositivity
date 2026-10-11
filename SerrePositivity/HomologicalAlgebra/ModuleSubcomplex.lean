module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Subcomplexes specified by submodules

A degreewise family of submodules stable under the differential gives a
subcomplex and a quotient complex of modules, with their canonical maps.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.ModuleSubcomplex

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ)
variable (N : ∀ i : ℤ, Submodule R (P.X i))
variable (hN : ∀ i j, ∀ x ∈ N i, P.d i j x ∈ N j)

def subcomplex : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (N i)
  d i j := ModuleCat.ofHom (((P.d i j).hom.comp (N i).subtype).codRestrict (N j)
    (fun x => hN i j x x.2))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change P.d i j x = 0
    rw [P.shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change P.d j k (P.d i j x) = 0
    have h := congrArg (fun f => f x) (P.d_comp_d i j k)
    exact h

def quotient : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (P.X i ⧸ N i)
  d i j := ModuleCat.ofHom ((N i).mapQ (N j) (P.d i j).hom (hN i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (N i).mkQ_surjective x
    change (N j).mkQ (P.d i j x) = 0
    rw [P.shape i j hij]
    exact (N j).mkQ.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (N i).mkQ_surjective x
    change (N k).mkQ (P.d j k (P.d i j x)) = 0
    have h : P.d j k (P.d i j x) = 0 :=
      congrArg (fun f => f x) (P.d_comp_d i j k)
    rw [h]
    exact (N k).mkQ.map_zero

def inclusion : subcomplex P N hN ⟶ P where
  f i := ModuleCat.ofHom (N i).subtype
  comm' i j _ := by rfl

def projection : P ⟶ quotient P N hN where
  f i := ModuleCat.ofHom (N i).mkQ
  comm' i j _ := by rfl

lemma inclusion_projection : inclusion P N hN ≫ projection P N hN = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero (p := N i)).mpr x.2

def shortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (inclusion P N hN) (projection P N hN) (inclusion_projection P N hN)

lemma inclusion_injective (i : ℤ) : Function.Injective ((inclusion P N hN).f i) :=
  Submodule.subtype_injective _

lemma projection_surjective (i : ℤ) : Function.Surjective ((projection P N hN).f i) :=
  (N i).mkQ_surjective

lemma component_exact (i : ℤ) : Function.Exact
    ((inclusion P N hN).f i) ((projection P N hN).f i) := by
  intro x
  change (Submodule.Quotient.mk x : P.X i ⧸ N i) = 0 ↔ ∃ y : N i, (y : P.X i) = x
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem shortExact : (shortComplex P N hN).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact (component_exact P N hN i x).mp hx
  · exact (ModuleCat.mono_iff_injective _).mpr (inclusion_injective P N hN i)
  · exact (ModuleCat.epi_iff_surjective _).mpr (projection_surjective P N hN i)

/-- Killing an acyclic subcomplex does not change homology. -/
theorem quasiIso_projection
    (hacyclic : ∀ i, IsZero ((subcomplex P N hN).homology i)) :
    QuasiIso (projection P N hN) := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let hS := shortExact P N hN
  have hm := (hS.homology_exact₂ i).mono_g_iff.mpr
    ((hacyclic i).eq_zero_of_src _)
  have he := (hS.homology_exact₃ i (i + 1) (by simp)).epi_f_iff.mpr
    ((hacyclic (i + 1)).eq_zero_of_tgt _)
  let : Mono (HomologicalComplex.homologyMap (projection P N hN) i) := hm
  let : Epi (HomologicalComplex.homologyMap (projection P N hN) i) := he
  exact isIso_of_mono_of_epi _

end SerrePositivity.ModuleSubcomplex
