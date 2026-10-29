module

public import SerrePositivity.CommutativeAlgebra.AdicCompletenessSup
public import SerrePositivity.CommutativeAlgebra.AdicModuleMaps
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import SerrePositivity.CommutativeAlgebra.AdicCompletionKernelClosure
public import SerrePositivity.CommutativeAlgebra.AdicCompletionFinite
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import SerrePositivity.CommutativeAlgebra.FiniteNormalizationTools
public import SerrePositivity.CommutativeAlgebra.AdicCompletenessClosedQuotient
public import Mathlib.RingTheory.Flat.Equalizer

/-! # 完備 Kähler 微分

概要：イデアル `I ⊆ S` に沿う Kähler 微分の完備化 `Ω̂_{S/k} = (Ω_{S/k})^∧_I` について
- 閉ファイバー `S/I` が `k` 上本質的に有限型で `S` が `I` 進前完備なら、`Ω̂_{S/k}` は `S` 上有限。
- `S` が Noether なら、有限な `Ω̂_{S/k}` は普遍微分の像で張られる（係数拡大しても同じ）。
- `S/R` が本質的に有限型で `S` が Noether 局所・`I` 進完備なら、`Ω_{S/R}` は `I` 進完備で、
  推移列 `(S ⊗_R Ω_{R/k})^∧ → Ω̂_{S/k} → Ω_{S/R} → 0` は完全（`Ω̂_{S/k}` が有限のとき）。
方針：有限性は余接の右完全列で `Ω_{S/k}/I Ω_{S/k}` の有限性に帰着する。推移列の完全性は、Mathlib の
`KaehlerDifferential.exact_mapBaseChange_map` を完備化し、有限な完備化の完全性（`AdicCompletionKernelClosure`）を使う。
規約：`Ω_{S/k}` 自身の有限生成性は仮定しない。
使われ方：冪級数環の完備微分（`PowerSeries/Differential`）、中間係数体上の完備微分（`Cofinite*`）、Cohen–Gabber。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Finite

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- 有限生成イデアルの閉ファイバーが有限型なら、通常の微分のイデアル商は有限。 -/
theorem moduleFinite_kaehler_quotient_of_finiteType_fiber
    (I : Ideal S) (hI : I.FG) [Algebra.EssFiniteType k (S ⧸ I)] :
    Module.Finite S
      (KaehlerDifferential k S ⧸ I • (⊤ : Submodule S (KaehlerDifferential k S))) := by
  let Q := S ⧸ I
  let K := RingHom.ker (algebraMap S Q)
  have hK : K.FG := by
    simpa only [K, Q, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hI
  let : Module.Finite S K := Module.Finite.of_fg hK
  let : Module.Finite S K.Cotangent :=
    Module.Finite.of_surjective K.toCotangent K.toCotangent_surjective
  let : Module.Finite S (KaehlerDifferential k Q) := Module.Finite.trans Q _
  have hs : Function.Surjective (algebraMap S Q) := Ideal.Quotient.mk_surjective
  let : Module.Finite S (TensorProduct S Q (KaehlerDifferential k S)) :=
    Module.Finite.of_exact
      (f := KaehlerDifferential.kerCotangentToTensor k S Q)
      (g := (KaehlerDifferential.mapBaseChange k S Q).restrictScalars S)
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k S Q hs)
      (KaehlerDifferential.mapBaseChange_surjective k S Q hs)
  exact Module.Finite.of_surjective
    (TensorProduct.quotTensorEquivQuotSMul (KaehlerDifferential k S) I).toLinearMap
    (TensorProduct.quotTensorEquivQuotSMul (KaehlerDifferential k S) I).surjective

/-- 有限型の閉ファイバーと基底の前完備性から完備微分の有限性を得る。 -/
theorem moduleFinite_completedKaehler_of_finiteType_fiber
    (I : Ideal S) (hI : I.FG) [IsPrecomplete I S] [Algebra.EssFiniteType k (S ⧸ I)] :
    Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) := by
  let : Module.Finite S
      (KaehlerDifferential k S ⧸ I • (⊤ : Submodule S (KaehlerDifferential k S))) :=
    moduleFinite_kaehler_quotient_of_finiteType_fiber I hI
  exact moduleFinite_adicCompletion_of_finite_quotient I hI

end Finite

section Generation

open scoped TensorProduct

/-- 有限な完備化は元の加群の像で生成される。元の加群の有限性は不要。 -/
theorem span_range_adicCompletion_of_eq_top
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R (AdicCompletion I M)] :
    Submodule.span R (Set.range (AdicCompletion.of I M)) = ⊤ := by
  let P := Submodule.span R (Set.range (AdicCompletion.of I M))
  let : IsHausdorff I (AdicCompletion I M ⧸ P) := IsHausdorff.of_le_jacobson I _ hI
  have hq : P.mkQ = 0 := by
    apply adicCompletion_linearMap_ext_of_of I I.fg_of_isNoetherianRing
    ext m
    exact (Submodule.Quotient.mk_eq_zero P).mpr (Submodule.subset_span ⟨m, rfl⟩)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero P).mp (LinearMap.congr_fun hq x)

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- 普遍導分をイデアル進完備化へ送る。 -/
def completedKaehlerDerivation (I : Ideal S) :
    Derivation k S (AdicCompletion I (KaehlerDifferential k S)) :=
  (AdicCompletion.of I _).compDer (KaehlerDifferential.D k S)

@[simp] theorem completedKaehlerDerivation_apply (I : Ideal S) (s : S) :
    completedKaehlerDerivation (k := k) I s =
      AdicCompletion.of I _ (KaehlerDifferential.D k S s) := rfl

/-- 有限な完備微分は普遍微分の像で生成される。 -/
theorem span_range_completedKaehlerDerivation_eq_top [IsNoetherianRing S]
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    Submodule.span S (Set.range (completedKaehlerDerivation (k := k) I)) = ⊤ := by
  have h := congrArg (fun P : Submodule S (KaehlerDifferential k S) ↦
    P.map (AdicCompletion.of I _)) (KaehlerDifferential.span_range_derivation k S)
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  exact h.trans (by simpa only [← LinearMap.coe_range, Submodule.span_eq] using
    span_range_adicCompletion_of_eq_top (M := KaehlerDifferential k S) I hI)

variable (L : Type*) [CommRing L] [Algebra S L] [Algebra k L] [IsScalarTower k S L]

/-- 完備普遍導分を同じ環上で係数拡大する。 -/
def baseChangeCompletedKaehlerDerivation (I : Ideal S) :
    Derivation k S (L ⊗[S] AdicCompletion I (KaehlerDifferential k S)) :=
  (TensorProduct.mk S L _ 1).compDer (completedKaehlerDerivation (k := k) I)

@[simp] theorem baseChangeCompletedKaehlerDerivation_apply (I : Ideal S) (s : S) :
    baseChangeCompletedKaehlerDerivation (k := k) L I s =
      1 ⊗ₜ[S] AdicCompletion.of I _ (KaehlerDifferential.D k S s) := rfl

/-- 係数拡大した有限完備微分も、同じ普遍微分の像で生成される。 -/
theorem span_range_baseChangeCompletedKaehlerDerivation_eq_top [IsNoetherianRing S]
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    Submodule.span L (Set.range (baseChangeCompletedKaehlerDerivation (k := k) L I)) = ⊤ := by
  have h := congrArg (fun P : Submodule S (AdicCompletion I (KaehlerDifferential k S)) ↦
    P.baseChange L) (span_range_completedKaehlerDerivation_eq_top (k := k) I hI)
  rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h

end Generation

section Relative

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
  (I : Ideal S) (hI : I ≤ IsLocalRing.maximalIdeal S) [IsAdicComplete I S]

include hI

/-- 有限型相対微分の有限性はMathlibから、完備性は有限加群の共通APIから供給する。 -/
theorem isAdicComplete_relativeDifferential : IsAdicComplete I (KaehlerDifferential R S) :=
  isAdicComplete_finite_of_ideal_complete I hI (KaehlerDifferential R S)

/-- 通常の相対微分とそのイデアル進完備化の同型。 -/
def relativeDifferentialCompletionEquiv :
    KaehlerDifferential R S ≃ₗ[S] AdicCompletion I (KaehlerDifferential R S) := by
  let : IsAdicComplete I (KaehlerDifferential R S) := isAdicComplete_relativeDifferential I hI
  exact AdicCompletion.ofLinearEquiv I (KaehlerDifferential R S)

@[simp] theorem relativeDifferentialCompletionEquiv_apply (ω : KaehlerDifferential R S) :
    relativeDifferentialCompletionEquiv I hI ω = AdicCompletion.of I (KaehlerDifferential R S) ω :=
  rfl

@[simp] theorem relativeDifferentialCompletionEquiv_symm_of (ω : KaehlerDifferential R S) :
    (relativeDifferentialCompletionEquiv I hI).symm
      (AdicCompletion.of I (KaehlerDifferential R S) ω) = ω :=
  (relativeDifferentialCompletionEquiv I hI).symm_apply_apply ω

variable (k : Type*) [CommRing k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- 完備化した係数制限を、完備な通常の相対微分に戻す写像。 -/
def completedDifferentialRestriction :
    AdicCompletion I (KaehlerDifferential k S) →ₗ[S] KaehlerDifferential R S :=
  (relativeDifferentialCompletionEquiv I hI).symm.toLinearMap.comp
    ((AdicCompletion.map I (KaehlerDifferential.map k R S S)).restrictScalars S)

@[simp] theorem completedDifferentialRestriction_of (ω : KaehlerDifferential k S) :
    completedDifferentialRestriction I hI k (AdicCompletion.of I (KaehlerDifferential k S) ω) =
      KaehlerDifferential.map k R S S ω := by
  change (relativeDifferentialCompletionEquiv I hI).symm
    (AdicCompletion.map I (KaehlerDifferential.map k R S S)
      (AdicCompletion.of I (KaehlerDifferential k S) ω)) = _
  rw [AdicCompletion.map_of, relativeDifferentialCompletionEquiv_symm_of]

/-- 完備化した元の微分を、相対微分の普遍導分へ送る。 -/
@[simp] theorem completedDifferentialRestriction_D (s : S) :
    completedDifferentialRestriction I hI k
      (AdicCompletion.of I (KaehlerDifferential k S) (KaehlerDifferential.D k S s)) =
        KaehlerDifferential.D R S s := by
  rw [completedDifferentialRestriction_of, KaehlerDifferential.map_D]
  rfl

/-- 係数制限の全射性は完備化でも保たれる。絶対微分の有限性は不要。 -/
theorem completedDifferentialRestriction_surjective :
    Function.Surjective (completedDifferentialRestriction (R := R) I hI k) := by
  exact (relativeDifferentialCompletionEquiv I hI).symm.surjective.comp
    (AdicCompletion.map_surjective I (KaehlerDifferential.map_surjective k R S))

end Relative

section Transitivity

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
  (I : Ideal S) (hI : I ≤ IsLocalRing.maximalIdeal S) [IsAdicComplete I S]
  (k : Type*) [CommRing k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- 通常の推移列の最初の写像を、テンソル積のS上の完備化へ延長する。 -/
def completedDifferentialBaseChange :
    AdicCompletion I (TensorProduct R S (KaehlerDifferential k R)) →ₗ[S]
      AdicCompletion I (KaehlerDifferential k S) :=
  (AdicCompletion.map I (KaehlerDifferential.mapBaseChange k R S)).restrictScalars S

omit [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete I S] in
@[simp] theorem completedDifferentialBaseChange_of
    (ω : TensorProduct R S (KaehlerDifferential k R)) :
    completedDifferentialBaseChange I k (AdicCompletion.of I _ ω) =
      AdicCompletion.of I _ (KaehlerDifferential.mapBaseChange k R S ω) :=
  AdicCompletion.map_of I _ ω

/-- 通常の相対微分への比較同型は核を変えない。 -/
theorem completedDifferentialRestriction_eq_zero_iff
    (x : AdicCompletion I (KaehlerDifferential k S)) :
    completedDifferentialRestriction (R := R) I hI k x = 0 ↔
      AdicCompletion.map I (KaehlerDifferential.map k R S S) x = 0 := by
  constructor
  · intro h
    apply (relativeDifferentialCompletionEquiv (R := R) I hI).symm.injective
    exact h.trans ((relativeDifferentialCompletionEquiv I hI).symm.map_zero).symm
  · intro h
    change (relativeDifferentialCompletionEquiv I hI).symm
      (AdicCompletion.map I (KaehlerDifferential.map k R S S) x) = 0
    rw [h, map_zero]

/-- 完備絶対微分の有限性を供給すると、閉包を除いて実際の像と核が一致する。
有限性を与える具体的な冪級数・有限代数の証明は、この一般入口と分ける。 -/
theorem range_completedDifferentialBaseChange_eq_ker
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    LinearMap.range (completedDifferentialBaseChange (R := R) I k) =
      LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) := by
  have he := adicCompletion_map_exact_of_finite_completion I
    (hI.trans (IsLocalRing.maximalIdeal_le_jacobson ⊥))
    (KaehlerDifferential.mapBaseChange k R S) (KaehlerDifferential.map k R S S)
    (KaehlerDifferential.exact_mapBaseChange_map k R S)
    (KaehlerDifferential.map_surjective k R S)
  apply Submodule.ext
  intro x
  change x ∈ LinearMap.range
    ((AdicCompletion.map I (KaehlerDifferential.mapBaseChange k R S)).restrictScalars S) ↔ _
  rw [← he.linearMap_ker_eq]
  exact (completedDifferentialRestriction_eq_zero_iff I hI k x).symm

end Transitivity

section Primary

universe u
open IsLocalRing


/-- 共通の剰余体と準素性から、パラメータイデアルに沿う完備微分の有限性を得る。 -/
theorem moduleFinite_completedKaehler_of_primary_common_residue
    {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (hres : Function.Surjective ((residue S).comp (algebraMap k S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) := by
  have hIm : I ≤ maximalIdeal S := by rw [← hI]; exact Ideal.le_radical
  let : IsAdicComplete I S := isAdicComplete_finite_of_le_maximalIdeal I hIm
  let : Module.Finite k (S ⧸ I) := finite_quotient_of_common_residue_primary hres I hI
  exact moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing

/-- 有限型の閉ファイバーを実際に確認すると、完備した推移列の像と核が一致する。 -/
theorem range_completedDifferentialBaseChange_eq_ker_of_finiteType_fiber
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal S) (hI : I ≤ maximalIdeal S) [IsAdicComplete I S]
    [Algebra.EssFiniteType k (S ⧸ I)] :
    LinearMap.range (completedDifferentialBaseChange (R := R) I k) =
      LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) := by
  let : Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) :=
    moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing
  exact range_completedDifferentialBaseChange_eq_ker I hI k

end Primary

section Kernel

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 完備中項が有限なら、有限族で生成された核も同じ族の完備化の像で生成される。 -/
theorem ker_adicCompletion_map_eq_span_of_ker_eq_span [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R (AdicCompletion I M)]
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    {ι : Type*} (c : ι → M) (hker : LinearMap.ker g = Submodule.span R (Set.range c)) :
    LinearMap.ker ((AdicCompletion.map I g).restrictScalars R) =
      Submodule.span R (Set.range (fun i ↦ AdicCompletion.of I M (c i))) := by
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let P := Submodule.span R (Set.range (fun i ↦ AdicCompletion.of I M (c i)))
  let : IsHausdorff I (AdicCompletion I M ⧸ P) := IsHausdorff.of_le_jacobson I _ hI
  have hc := isClosed_submodule_adic_of_hausdorff_quotient I P
  have he := closure_ker_image_eq_ker_adicCompletion_map I I.fg_of_isNoetherianRing g hg
  rw [hker, Submodule.map_span, ← Set.range_comp] at he
  change closure (P : Set (AdicCompletion I M)) = _ at he
  rw [hc.closure_eq] at he
  exact SetLike.coe_injective he.symm

/-- 平坦な係数拡大で核の生成族を同じテンソルの像へ移す。 -/
theorem ker_baseChange_eq_span_of_ker_eq_span
    (L : Type*) [CommRing L] [Algebra R L] [Module.Flat R L]
    (g : M →ₗ[R] N) {ι : Type*} (c : ι → M)
    (hker : LinearMap.ker g = Submodule.span R (Set.range c)) :
    LinearMap.ker (g.baseChange L) = Submodule.span L
      (Set.range (fun i ↦ (1 : L) ⊗ₜ[R] c i)) := by
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L g) = _
  rw [Module.Flat.ker_lTensor_eq]
  change (LinearMap.ker g).baseChange L = _
  rw [hker, Submodule.baseChange_span, ← Set.range_comp]
  rfl

end Kernel

end SerrePositivity
