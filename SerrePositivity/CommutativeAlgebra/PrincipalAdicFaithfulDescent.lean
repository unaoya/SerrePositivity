module

public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescentAlgebra

/-! # G1：主元の環商を直接使う全射降下 -/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- 主元の環商に対するMathlibの標準剰余代数構造。 -/
abbrev principalAdicQuotientAlgebra (a : R) (S : Type*) [CommRing S] [Algebra R S] :
    Algebra (R ⧸ Ideal.span {a}) (S ⧸ Ideal.span {algebraMap R S a}) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton_self _))

attribute [local instance] principalAdicQuotientAlgebra

/-- 加群の剰余と、主元の像で割った環商の比較。 -/
def principalAdicReductionEquiv (a : R) (S : Type*) [CommRing S] [Algebra R S] :
    AdicReduction (Ideal.span {a}) S ≃ₗ[R ⧸ Ideal.span {a}]
      S ⧸ Ideal.span {algebraMap R S a} :=
  let e := (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map (Ideal.span {a}))) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {a}).map (algebraMap R S)) ≪≫ₗ
    (Ideal.quotientEquivAlgOfEq R
      (by simp only [Ideal.map_span, Set.image_singleton])).toLinearEquiv
  { e.toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := (Ideal.span {a} • (⊤ : Submodule R S)).mkQ_surjective x
      rfl }

@[simp] theorem principalAdicReductionEquiv_mkQ
    (a : R) (S : Type*) [CommRing S] [Algebra R S] (x : S) :
    principalAdicReductionEquiv a S ((Ideal.span {a} • (⊤ : Submodule R S)).mkQ x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R S a}) x := rfl

@[simp] theorem principalAdicReductionEquiv_symm_mk
    (a : R) (S : Type*) [CommRing S] [Algebra R S] (x : S) :
    (principalAdicReductionEquiv a S).symm
      (Ideal.Quotient.mk (Ideal.span {algebraMap R S a}) x) =
        (Ideal.span {a} • (⊤ : Submodule R S)).mkQ x := rfl

variable {S C : Type*} [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]

/-- f mod aを、S/(a)とC/(a)の間のR/(a)線形写像として公開する。 -/
def principalAdicReductionMap (a : R) (f : S →ₐ[R] C) :
    (S ⧸ Ideal.span {algebraMap R S a}) →ₗ[R ⧸ Ideal.span {a}]
      C ⧸ Ideal.span {algebraMap R C a} :=
  (principalAdicReductionEquiv a C).toLinearMap ∘ₗ
    adicReductionMap (Ideal.span {a}) f.toLinearMap ∘ₗ
      (principalAdicReductionEquiv a S).symm.toLinearMap

@[simp] theorem principalAdicReductionMap_mk (a : R) (f : S →ₐ[R] C) (x : S) :
    principalAdicReductionMap a f (Ideal.Quotient.mk (Ideal.span {algebraMap R S a}) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C a}) (f x) := rfl

/-- 主元の像に関する前完備性・分離性だけから適用できる全射降下。 -/
theorem surjective_algHom_of_faithfullyFlat_principalReduction
    (a : R) [IsPrecomplete (Ideal.span {algebraMap R S a}) S]
    [IsHausdorff (Ideal.span {algebraMap R C a}) C]
    (E : Type*) [AddCommGroup E] [Module (R ⧸ Ideal.span {a}) E]
    [Module.FaithfullyFlat (R ⧸ Ideal.span {a}) E] (f : S →ₐ[R] C)
    (h : Function.Surjective ((principalAdicReductionMap a f).lTensor E)) :
    Function.Surjective f := by
  have hS : IsPrecomplete ((Ideal.span {a}).map (algebraMap R S)) S := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      (inferInstance : IsPrecomplete (Ideal.span {algebraMap R S a}) S)
  have hC : IsHausdorff ((Ideal.span {a}).map (algebraMap R C)) C := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      (inferInstance : IsHausdorff (Ideal.span {algebraMap R C a}) C)
  have : IsPrecomplete (Ideal.span {a}) S :=
    (IsPrecomplete.map_algebraMap_iff (S := S) (M := S)).mp hS
  have : IsHausdorff (Ideal.span {a}) C :=
    (IsHausdorff.map_algebraMap_iff (S := C) (M := C)).mp hC
  have hb := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
    (R ⧸ Ideal.span {a}) E (principalAdicReductionMap a f)).mp h
  apply surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) (f := f.toLinearMap)
  intro y
  obtain ⟨x, hx⟩ := hb (principalAdicReductionEquiv a C y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨x, (principalAdicReductionEquiv a C).injective ?_⟩
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    principalAdicReductionEquiv_mkQ, principalAdicReductionMap_mk] using hx

/-- BS要求G1の正確な環商を使う入口。a=(p:R)にも素数性なしで適用できる。 -/
theorem surjective_algHom_of_principal_residue_baseChange
    (a : R) (R' : Type*) [CommRing R'] [Algebra R R']
    [IsPrecomplete (Ideal.span {algebraMap R S a}) S]
    [IsHausdorff (Ideal.span {algebraMap R C a}) C]
    [Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] R')]
    (f : S →ₐ[R] C)
    (h : Function.Surjective
      ((principalAdicReductionMap a f).lTensor ((R ⧸ Ideal.span {a}) ⊗[R] R'))) :
    Function.Surjective f :=
  surjective_algHom_of_faithfullyFlat_principalReduction a _ f h

end SerrePositivity
