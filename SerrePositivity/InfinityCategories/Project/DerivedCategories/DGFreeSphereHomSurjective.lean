module
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：自由 sphere の全次数 Hom は次数別全射な後合成を保つ。
方針：実全次数 Hom と評価・余積の既存の普遍性を使う。
規約：全 dg 自然性と元の後合成射を保つ。使われ方：strict cell lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgComplexSphereHomElement_postcompose
    (R : Type u) [CommRing R] {K L : Complex R} (f : K ⟶ L) (n p : ℤ)
    (z : (homComplex R (complexSphere R n) K).X p) :
    complexSphereHomElementEquiv R L n p
      ((homPostcompose (complexSphere R n) f).f p z) =
        f.f (n + p) (complexSphereHomElementEquiv R K n p z) := by
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z (n + p) rfl
  change complexSphereHomElementEquiv R L n p
    ((Cochain.fromSingleMk a rfl).comp (Cochain.ofHom f) (add_zero p)) = _
  rw [← Cochain.fromSingleMk_postcomp]
  change (Cochain.fromSingleEquiv (rfl : n + p = n + p)
    (Cochain.fromSingleMk (a ≫ f.f (n + p)) rfl)) (1 : R) =
      f.f (n + p) ((Cochain.fromSingleEquiv (rfl : n + p = n + p)
        (Cochain.fromSingleMk a rfl)) (1 : R))
  rw [Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk]
  rfl
lemma dgComplexSphereHom_postcompose_surjective
    (R : Type u) [CommRing R] {K L : Complex R} (f : K ⟶ L)
    (hf : ∀ p, Function.Surjective (f.f p)) (n p : ℤ) :
    Function.Surjective ((homPostcompose (complexSphere R n) f).f p) := by
  intro z
  obtain ⟨a, ha⟩ := hf (n + p) (complexSphereHomElementEquiv R L n p z)
  refine ⟨(complexSphereHomElementEquiv R K n p).symm a, ?_⟩
  apply (complexSphereHomElementEquiv R L n p).injective
  rw [dgComplexSphereHomElement_postcompose, Equiv.apply_symm_apply, ha]
lemma dgModuleFreeSphereHom_postcompose_surjective
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (x : D) (n : ℤ) {M N : ModuleCategory R D} (q : M ⟶ N)
    (hq : moduleDegreewiseSurjective R D q) (p : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex R) (freeSphere R D x n) q).f p) := by
  intro z
  let eM := freeHomIso R D x (complexSphere R n) (ForgetEnrichment.to (Complex R) M)
  let eN := freeHomIso R D x (complexSphere R n) (ForgetEnrichment.to (Complex R) N)
  let r := homPostcompose (complexSphere R n) ((moduleEvaluation R D x).map q)
  obtain ⟨a, ha⟩ := dgComplexSphereHom_postcompose_surjective R
    ((moduleEvaluation R D x).map q) (hq x) n p (eN.hom.f p z)
  refine ⟨eM.inv.f p a, ?_⟩
  apply (ModuleCat.mono_iff_injective (eN.hom.f p)).mp (inferInstance)
  have hnat := congrArg (fun c => c.f p (eM.inv.f p a))
    (freeHomIso_naturality_target R D x (complexSphere R n) q)
  change eN.hom.f p
      ((eHomWhiskerLeft (Complex R) (freeSphere R D x n) q).f p (eM.inv.f p a)) =
    r.f p (eM.hom.f p (eM.inv.f p a)) at hnat
  have hi := congrArg (fun c => c.f p a) eM.inv_hom_id
  change eM.hom.f p (eM.inv.f p a) = a at hi
  exact hnat.trans ((congrArg (r.f p) hi).trans ha)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
