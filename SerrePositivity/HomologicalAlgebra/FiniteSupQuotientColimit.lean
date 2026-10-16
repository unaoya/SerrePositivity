module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotients by arbitrary ideal suprema as finite-subset module colimits -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] {σ : Type u} (I : σ → Ideal R)

/-- The original quotient maps for inclusions of finite subsets. -/
def finiteSupQuotientDiagram : Finset σ ⥤ ModuleCat.{u} R where
  obj s := ModuleCat.of R (R ⧸ s.sup I)
  map {s t} h := ModuleCat.ofHom (Submodule.factor (Finset.sup_mono (f := I) (leOfHom h)))
  map_id s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

/-- Standard maps from each finite ideal quotient to the full quotient. -/
def finiteSupQuotientCocone : Cocone (finiteSupQuotientDiagram I) where
  pt := ModuleCat.of R (R ⧸ ⨆ a, I a)
  ι :=
    { app := fun s => ModuleCat.ofHom (Submodule.factor
        (Finset.sup_le (fun a _ => le_iSup I a)))
      naturality := by
        intro s t h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
        rfl }

/-- The full quotient satisfies the colimit universal property, including an empty index family. -/
def finiteSupQuotient_isColimit :
    IsColimit (finiteSupQuotientCocone I) := by
  classical
  let F := finiteSupQuotientDiagram I
  let f (c : Cocone F) : R →ₗ[R] c.pt :=
    (c.ι.app ∅).hom.comp (Finset.sup (∅ : Finset σ) I).mkQ
  have hf (c : Cocone F) : (⨆ a, I a) ≤ LinearMap.ker (f c) := by
    apply iSup_le
    intro a x hx
    have hc := c.w (homOfLE (Finset.empty_subset ({a} : Finset σ)))
    have hv := congrArg (fun g => g.hom ((Finset.sup (∅ : Finset σ) I).mkQ x)) hc
    have hx' : x ∈ ({a} : Finset σ).sup I := by simpa using hx
    let y : F.obj {a} := (Finset.sup ({a} : Finset σ) I).mkQ x
    have hz : y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx'
    change (c.ι.app {a}).hom y = (f c) x at hv
    rw [hz, map_zero] at hv
    exact hv.symm
  let d (c : Cocone F) := ModuleCat.ofHom ((⨆ a, I a).liftQ (f c) (hf c))
  refine { desc := d, fac := ?_, uniq := ?_ }
  · intro c s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (f c) x = (c.ι.app s).hom ((s.sup I).mkQ x)
    exact (congrArg (fun g => g.hom ((Finset.sup (∅ : Finset σ) I).mkQ x))
      (c.w (homOfLE (Finset.empty_subset s)))).symm
  · intro c m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change m.hom ((⨆ a, I a).mkQ x) = (f c) x
    exact congrArg (fun g => g.hom ((Finset.sup (∅ : Finset σ) I).mkQ x)) (hm ∅)

/-- Canonical comparison with the actual categorical colimit. -/
def finiteSupQuotientColimitIso :
    colimit (finiteSupQuotientDiagram I) ≅ ModuleCat.of R (R ⧸ ⨆ a, I a) :=
  colimit.isoColimitCocone ⟨_, finiteSupQuotient_isColimit I⟩

/-- The comparison retains each original quotient map. -/
lemma finiteSupQuotientColimitIso_ι (s : Finset σ) :
    colimit.ι (finiteSupQuotientDiagram I) s ≫ (finiteSupQuotientColimitIso I).hom =
      (finiteSupQuotientCocone I).ι.app s :=
  colimit.isoColimitCocone_ι_hom ⟨_, finiteSupQuotient_isColimit I⟩ s

end SerrePositivity
