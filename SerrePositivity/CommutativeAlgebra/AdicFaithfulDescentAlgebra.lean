module

public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 環商を使うadic忠実平坦降下の入口 -/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- R/IからS/ISへの標準代数構造。Mathlibの構造を局所的に使う。 -/
abbrev adicQuotientAlgebra (I : Ideal R) (S : Type*) [CommRing S] [Algebra R S] :
    Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

attribute [local instance] adicQuotientAlgebra

/-- 加群商S/(I•S)と環商S/ISの、R/I線形な標準比較。 -/
def adicReductionEquivAlgebraQuotient (I : Ideal R) (S : Type*)
    [CommRing S] [Algebra R S] :
    AdicReduction I S ≃ₗ[R ⧸ I] S ⧸ I.map (algebraMap R S) :=
  let e := (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I)) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R S))
  { e.toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R S)).mkQ_surjective x
      rfl }

/-- 比較同型は標準商写像を保つ。 -/
@[simp] theorem adicReductionEquivAlgebraQuotient_mkQ (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra R S] (x : S) :
    adicReductionEquivAlgebraQuotient I S ((I • (⊤ : Submodule R S)).mkQ x) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) x := rfl

/-- 逆同型も標準代表元を保つ。 -/
@[simp] theorem adicReductionEquivAlgebraQuotient_symm_mk (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra R S] (x : S) :
    (adicReductionEquivAlgebraQuotient I S).symm
      (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
        (I • (⊤ : Submodule R S)).mkQ x := rfl

variable {S C : Type*} [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]

/-- R代数写像が環商の間に誘導するR/I線形写像。 -/
def adicAlgebraReductionMap (I : Ideal R) (f : S →ₐ[R] C) :
    (S ⧸ I.map (algebraMap R S)) →ₗ[R ⧸ I] C ⧸ I.map (algebraMap R C) :=
  (adicReductionEquivAlgebraQuotient I C).toLinearMap ∘ₗ
    adicReductionMap I f.toLinearMap ∘ₗ
      (adicReductionEquivAlgebraQuotient I S).symm.toLinearMap

/-- 誘導写像と元の代数写像の標準図式。 -/
@[simp] theorem adicAlgebraReductionMap_mk (I : Ideal R) (f : S →ₐ[R] C) (x : S) :
    adicAlgebraReductionMap I f (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk (I.map (algebraMap R C)) (f x) := rfl

/-- 二つの標準比較と剰余写像の可換図式。 -/
theorem adicAlgebraReductionMap_equiv (I : Ideal R) (f : S →ₐ[R] C) :
    adicAlgebraReductionMap I f ∘ₗ (adicReductionEquivAlgebraQuotient I S).toLinearMap =
      (adicReductionEquivAlgebraQuotient I C).toLinearMap ∘ₗ
        adicReductionMap I f.toLinearMap := by
  apply LinearMap.ext
  intro x
  change adicReductionEquivAlgebraQuotient I C
      (adicReductionMap I f.toLinearMap
        ((adicReductionEquivAlgebraQuotient I S).symm
          (adicReductionEquivAlgebraQuotient I S x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- S自身の前完備性・C自身の分離性から適用できる、環商による全射降下。 -/
theorem surjective_algHom_of_faithfullyFlat_adicReduction
    (I : Ideal R) [IsPrecomplete (I.map (algebraMap R S)) S]
    [IsHausdorff (I.map (algebraMap R C)) C]
    (E : Type*) [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.FaithfullyFlat (R ⧸ I) E] (f : S →ₐ[R] C)
    (h : Function.Surjective ((adicAlgebraReductionMap I f).lTensor E)) :
    Function.Surjective f := by
  have : IsPrecomplete I S :=
    (IsPrecomplete.map_algebraMap_iff (S := S) (M := S) (I := I)).mp inferInstance
  have : IsHausdorff I C :=
    (IsHausdorff.map_algebraMap_iff (S := C) (M := C) (I := I)).mp inferInstance
  have hb := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
    (R ⧸ I) E (adicAlgebraReductionMap I f)).mp h
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f.toLinearMap)
  intro y
  obtain ⟨x, hx⟩ := hb (adicReductionEquivAlgebraQuotient I C y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨x, (adicReductionEquivAlgebraQuotient I C).injective ?_⟩
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    adicReductionEquivAlgebraQuotient_mkQ, adicAlgebraReductionMap_mk] using hx

/-- G1：mod Iでのみ忠実平坦な環拡大への底変換後の全射性から降下する。 -/
theorem surjective_algHom_of_residue_baseChange
    (I : Ideal R) (R' : Type*) [CommRing R'] [Algebra R R']
    [IsPrecomplete (I.map (algebraMap R S)) S]
    [IsHausdorff (I.map (algebraMap R C)) C]
    [Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] R')]
    (f : S →ₐ[R] C)
    (h : Function.Surjective
      ((adicAlgebraReductionMap I f).lTensor ((R ⧸ I) ⊗[R] R'))) :
    Function.Surjective f :=
  surjective_algHom_of_faithfullyFlat_adicReduction I _ f h

end SerrePositivity
