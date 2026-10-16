module
public import SerrePositivity.HomologicalAlgebra.PrincipalQuotientResolution
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.TorNaturality

/-! # A regular principal quotient has no higher Tor with a regular coefficient module -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The two regular scalar actions make all higher Tor with R/(a) vanish. -/
lemma torModule_principalQuotient_subsingleton (a : R) (ha : IsSMulRegular R a)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M a)
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i
      (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a}))) M) := by
  let f : R →ₗ[R] R := a • LinearMap.id
  let g := principalQuotientLinearMap a
  have hf : Function.Injective f := ha
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have he : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      change Ideal.Quotient.mk (Ideal.span {a}) y = 0 at hy
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hy)
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      change Ideal.Quotient.mk (Ideal.span {a}) (a * x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨α, β, δ, _, hβδ, hδα, _, hαstd, _⟩ :=
    torModule_longExact_left_with_maps M f g hf hg he
  have hn (x : TorModule R 0 R M) : torModuleZeroEquiv R R M (α 0 x) =
      f.rTensor M (torModuleZeroEquiv R R M x) := by
    rw [hαstd 0]
    exact congrArg (fun k ↦ k.hom x)
      (torZeroIso_naturality_left (ModuleCat.ofHom f) (ModuleCat.of R M))
  have ht (z : R ⊗[R] M) :
      TensorProduct.lid R M (f.rTensor M z) = a • TensorProduct.lid R M z := by
    induction z using TensorProduct.inductionOn with
    | tmul r m => simp [f, smul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hαinj : Function.Injective (α 0) := by
    intro x y hxy
    apply (torModuleZeroEquiv R R M).injective
    apply (TensorProduct.lid R M).injective
    apply hM
    change a • TensorProduct.lid R M (torModuleZeroEquiv R R M x) =
      a • TensorProduct.lid R M (torModuleZeroEquiv R R M y)
    rw [← ht, ← ht, ← hn, ← hn, hxy]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  apply subsingleton_of_forall_eq 0
  intro x
  have hδx : δ j x = 0 := by
    cases j with
    | zero =>
      apply hαinj
      rw [map_zero]
      exact (hδα 0 (δ 0 x)).mpr ⟨x, rfl⟩
    | succ j =>
      let := torModule_subsingleton_of_flat (R := R) R M j
      exact Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (hβδ j x).mp hδx
  let := torModule_subsingleton_of_flat (R := R) R M j
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- Supply the existing derived quotient comparison's precise higher Tor input from regularity. -/
lemma scalarExtensionTorVanishing_principal_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : ModuleCat.{u} R) (hM : IsSMulRegular M a) :
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {a})) M := by
  intro i hi
  have := torModule_principalQuotient_subsingleton a ha M hM i hi
  exact ModuleCat.isZero_of_subsingleton _

/-- The same regularity inputs give the standard derived quotient comparison at every power. -/
lemma scalarExtensionTorVanishing_principal_pow_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : ModuleCat.{u} R) (hM : IsSMulRegular M a) (n : ℕ) :
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {a ^ n})) M :=
  scalarExtensionTorVanishing_principal_of_regular (a ^ n) (ha.pow n) M (hM.pow n)

/-- Derived reduction is the ordinary residue module, through the original standard augmentation. -/
def derivedQuotientModuleIsoOfRegular (a : R) (ha : IsSMulRegular R a)
    (M : ModuleCat.{u} R) (hM : IsSMulRegular M a) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj
        (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor (Ideal.span {a})).obj M) :=
  derivedQuotientModuleIso (Ideal.span {a}) M
    (scalarExtensionTorVanishing_principal_of_regular a ha M hM)

end SerrePositivity
