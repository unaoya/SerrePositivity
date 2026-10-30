module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # イデアルによる還元と忠実平坦な降下

## 概要

イデアル I による加群・代数の還元 M/IM と、その比較写像、主イデアル (a) の場合の還元代数 `principalAdicQuotientAlgebra` と同型 `principalAdicReductionEquiv`、還元が全射なら元の代数写像も全射になる降下定理（I 進完備な場合、主元版を含む）を与える。

## 方針

降下定理は一般のイデアルの版を本体にし、主イデアルの版は `Ideal.map_span` を介した系にする。還元の写像は Mathlib の `LinearMap.reduceModIdeal`、商の代数構造は Mathlib の instance `Ideal.Quotient.algebraQuotientMapQuotient` を使う。

## 規約

`adicQuotientAlgebra`・`principalAdicQuotientAlgebra`・`principalAdicReductionEquiv` は BhattScholze が多く使うので名前を残す。

## 使われ方

BhattScholze の semiperfectoid の全射性、完全平坦性の判定。
-/

@[expose] public noncomputable section

universe u

section AdicFaithfulDescentPart

namespace SerrePositivity
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Iで割った加群。R/I作用にはMathlibの既存instanceを使う。 -/
abbrev AdicReduction (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :=
  M ⧸ I • (⊤ : Submodule R M)

/-- 線形写像が剰余加群の間に誘導するR/I線形写像。 -/
def adicReductionMap (I : Ideal R) (f : M →ₗ[R] N) :
    AdicReduction I M →ₗ[R ⧸ I] AdicReduction I N :=
  LinearMap.reduceModIdeal I f

/-- 剰余写像は元の写像と標準商写像の図式を保つ。 -/
@[simp] theorem adicReductionMap_mkQ (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    adicReductionMap I f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := rfl

/-- 剰余写像が忠実平坦な加群による底変換後に全射なら、元の写像は全射。
始域の前完備性と終域の分離性だけを要し、Iの有限生成性は不要。 -/
theorem surjective_of_faithfullyFlat_adicReduction
    (I : Ideal R) [IsPrecomplete I M] [IsHausdorff I N]
    (E : Type*) [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.FaithfullyFlat (R ⧸ I) E] (f : M →ₗ[R] N)
    (h : Function.Surjective ((adicReductionMap I f).lTensor E)) :
    Function.Surjective f := by
  have hb := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
    (R ⧸ I) E (adicReductionMap I f)).mp h
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f)
  intro y
  obtain ⟨x, hx⟩ := hb y
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
  exact ⟨x, hx⟩

end SerrePositivity

end AdicFaithfulDescentPart

section AdicFaithfulDescentAlgebraPart

namespace SerrePositivity
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- R/IからS/ISへの標準代数構造。Mathlibの構造を局所的に使う。 -/
abbrev adicQuotientAlgebra (I : Ideal R) (S : Type*) [CommRing S] [Algebra R S] :
    Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Ideal.Quotient.algebraQuotientMapQuotient

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

end SerrePositivity

end AdicFaithfulDescentAlgebraPart

section PrincipalAdicFaithfulDescentPart

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

end PrincipalAdicFaithfulDescentPart

section PrincipalAdicReductionAlgebraPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
attribute [local instance] principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The standard quotient ring map, over the original quotient of the coefficient ring. -/
def principalAdicReductionAlgHom (f : S →ₐ[R] T) :
    (S ⧸ Ideal.span {algebraMap R S d}) →ₐ[R ⧸ Ideal.span {d}]
      T ⧸ Ideal.span {algebraMap R T d} := by
  let g : (S ⧸ Ideal.span {algebraMap R S d}) →+*
      T ⧸ Ideal.span {algebraMap R T d} :=
    Ideal.quotientMap (Ideal.span {algebraMap R T d}) f.toRingHom (by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change f (algebraMap R S d) ∈ Ideal.span {algebraMap R T d}
      rw [AlgHom.commutes]
      exact Ideal.mem_span_singleton_self _)
  exact
    { g with
      commutes' x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (f (algebraMap R S r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (algebraMap R T r)
        rw [AlgHom.commutes] }

/-- Its underlying linear map is exactly the previously used original residue map. -/
lemma principalAdicReductionAlgHom_toLinearMap (f : S →ₐ[R] T) :
    (principalAdicReductionAlgHom R d f).toLinearMap = principalAdicReductionMap d f := by
  apply LinearMap.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- On an original representative the map is the original algebra map followed by the quotient. -/
lemma principalAdicReductionAlgHom_mk (f : S →ₐ[R] T) (s : S) :
    principalAdicReductionAlgHom R d f (Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (f s) := rfl

end SerrePositivity

end PrincipalAdicReductionAlgebraPart

section PrincipalAdicReductionEquivPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
attribute [local instance] principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Use the original forward and inverse quotient algebra maps
without changing the quotient actions. -/
def principalAdicReductionAlgEquiv (e : S ≃ₐ[R] T) :
    (S ⧸ Ideal.span {algebraMap R S d}) ≃ₐ[R ⧸ Ideal.span {d}]
      T ⧸ Ideal.span {algebraMap R T d} := by
  let f := principalAdicReductionAlgHom R d e.toAlgHom
  let g := principalAdicReductionAlgHom R d e.symm.toAlgHom
  have hfg : f.comp g = AlgHom.id (R ⧸ Ideal.span {d}) _ := by
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e (e.symm t)) = Ideal.Quotient.mk _ t
    rw [e.apply_symm_apply]
  have hgf : g.comp f = AlgHom.id (R ⧸ Ideal.span {d}) _ := by
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e.symm (e s)) = Ideal.Quotient.mk _ s
    rw [e.symm_apply_apply]
  exact AlgEquiv.ofAlgHom f g hfg hgf

/-- On representatives this is the original algebra equivalence followed
by the original quotient. -/
lemma principalAdicReductionAlgEquiv_mk (e : S ≃ₐ[R] T) (s : S) :
    principalAdicReductionAlgEquiv R d e (Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (e s) := rfl

end SerrePositivity

end PrincipalAdicReductionEquivPart
