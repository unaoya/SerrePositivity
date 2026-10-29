module

public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.Adic.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 完備化の環としての性質

概要：
- 完備化 `R̂` から `I` 進完備な `R` 代数への代数準同型が一意に存在する。
- Noether 環の完備化は Noether。
- 有限生成な極大イデアルに沿う完備化の剰余体は、元の剰余体と同じ。
- 主イデアルの完備化の上で、生成元は正則。
- 二つのイデアル `I`、`J`（互いの冪が含まれる）に沿う完備化は同型。
方針：代数準同型は完備化の線形写像の外延性（`Adic/Completion/Basic`）から。Noether 性は商の Noether 性からの判定
（`AdicNoetherianCriterion`）、剰余体は Mathlib の `AdicCompletion.residueField_map_bijective_of_fg`。
規約：イデアルは有限生成。
使われ方：完備局所環の議論全般、Cohen–Gabber（イデアルの取り替え）、Bhatt–Scholze 側。Mathlib への提出候補。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicCompletionAlgebraUniversal

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type*) [CommRing R] (I : Ideal R) (hI : I.FG)
    (A : Type*) [CommRing A] [Algebra R A] [IsAdicComplete I A]

/-- Extend the original coefficient map to a complete R-algebra. -/
def adicCompletionToCompleteAlgebra : AdicCompletion I R →ₐ[R] A := by
  let f : AdicCompletion I R →ₗ[R] A :=
    (AdicCompletion.ofLinearEquiv I A).symm.toLinearMap.comp
      ((AdicCompletion.map I (Algebra.linearMap R A)).restrictScalars R)
  have hf (r : R) : f (algebraMap R (AdicCompletion I R) r) = algebraMap R A r := by
    change (AdicCompletion.ofLinearEquiv I A).symm
      (AdicCompletion.map I (Algebra.linearMap R A) (AdicCompletion.of I R r)) = _
    rw [AdicCompletion.map_of]
    exact (AdicCompletion.ofLinearEquiv I A).symm_apply_apply _
  apply AlgHom.ofLinearMap f
  · simpa using hf 1
  · intro x y
    have he : f.comp (LinearMap.mulRight R y) =
        (LinearMap.mulRight R (f y)).comp f := by
      apply adicCompletion_linearMap_ext_of_of I hI
      apply LinearMap.ext
      intro r
      change f (algebraMap R (AdicCompletion I R) r * y) =
        f (algebraMap R (AdicCompletion I R) r) * f y
      rw [hf, ← Algebra.smul_def, f.map_smul, Algebra.smul_def]
    exact LinearMap.congr_fun he x

/-- The extension preserves the original map from every coefficient. -/
lemma adicCompletionToCompleteAlgebra_of (r : R) :
    adicCompletionToCompleteAlgebra R I hI A (algebraMap R (AdicCompletion I R) r) =
      algebraMap R A r :=
  (adicCompletionToCompleteAlgebra R I hI A).commutes r

include hI in
/-- Algebra maps from the completion to a complete algebra are unique. -/
lemma adicCompletion_algHom_ext (f g : AdicCompletion I R →ₐ[R] A) : f = g := by
  apply AlgHom.toLinearMap_injective
  apply adicCompletion_linearMap_ext_of_of I hI
  apply LinearMap.ext
  intro r
  exact (f.commutes r).trans (g.commutes r).symm

include hI in
/-- The adic completion has the expected algebra universal property. -/
lemma adicCompletion_existsUnique_algHom : ∃! _f : AdicCompletion I R →ₐ[R] A, True :=
  ⟨adicCompletionToCompleteAlgebra R I hI A, trivial,
    fun f _ => adicCompletion_algHom_ext R I hI A f _⟩

end AdicCompletionAlgebraUniversal

section AdicCompletionNoetherian

/-- Noether 環の任意のイデアルに関するイデアル進完備化は Noether 環である。 -/
theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact isNoetherianRing_adicCompletion_of_noetherian_quotient R I I.fg_of_isNoetherianRing

end AdicCompletionNoetherian

section AdicCompletionResidue

open IsLocalRing
variable {S K : Type*} [CommRing S] [IsLocalRing S] [Field K]

/-- 完備化の剰余体を指定体へ同定する。 -/
noncomputable def adicCompletionTargetResidueEquiv
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K) :
    letI : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
      AdicCompletion.isLocalRing_of_fg hfg
    ResidueField (AdicCompletion (maximalIdeal S) S) ≃+* K := by
  let : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
    AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S (AdicCompletion (maximalIdeal S) S)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  exact (RingEquiv.ofBijective (ResidueField.map
    (algebraMap S (AdicCompletion (maximalIdeal S) S)))
    (AdicCompletion.residueField_map_bijective_of_fg hfg)).symm.trans e

/-- 元の環の元は、指定体で元の剰余体同型による値を持つ。 -/
theorem adicCompletionTargetResidueEquiv_apply
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K) (s : S) :
    letI : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
      AdicCompletion.isLocalRing_of_fg hfg
    adicCompletionTargetResidueEquiv hfg e
      (residue _ (algebraMap S (AdicCompletion (maximalIdeal S) S) s)) = e (residue S s) := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  let r : ResidueField S ≃+* ResidueField C := RingEquiv.ofBijective
    (ResidueField.map (algebraMap S C)) (AdicCompletion.residueField_map_bijective_of_fg hfg)
  change e (r.symm (residue C (algebraMap S C s))) = _
  rw [← ResidueField.map_residue (algebraMap S C)]
  change e (r.symm (r (residue S s))) = _
  rw [r.symm_apply_apply]

/-- 指定体への同型は、基底の剰余体からの係数写像とも両立する。 -/
theorem adicCompletionTargetResidueEquiv_base_map
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Algebra (ResidueField B) K]
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x)
    (x : ResidueField B) :
    let C := AdicCompletion (maximalIdeal S) S
    letI : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
    letI : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
    letI : IsLocalHom (algebraMap B C) := by
      rw [IsScalarTower.algebraMap_eq B S C]
      infer_instance
    adicCompletionTargetResidueEquiv hfg e (ResidueField.map (algebraMap B C) x) =
      algebraMap (ResidueField B) K x := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  change adicCompletionTargetResidueEquiv hfg e
    (ResidueField.map (algebraMap B C) (residue B b)) = _
  rw [ResidueField.map_residue, IsScalarTower.algebraMap_apply B S C,
    adicCompletionTargetResidueEquiv_apply, ← ResidueField.map_residue]
  exact he (residue B b)

end AdicCompletionResidue

section AdicCompletionRegular

/-- 正則元が生成する主イデアルについて、完備化上でもその元は正則。
第 `n+1` 座標で生成元をキャンセルし、第 `n` 座標が零であることを示す。 -/
theorem isSMulRegular_adicCompletion_span_singleton
    (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) :
    IsSMulRegular (AdicCompletion (Ideal.span {a}) R)
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨v, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {a}) R x
  apply AdicCompletion.ext_evalₐ
  intro n
  have hx' : a * v.val (n + 1) ∈ (Ideal.span {a}) ^ (n + 1) := by
    have he := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hx
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (n + 1)) (a * v.val (n + 1)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hv : v.val (n + 1) = a ^ n * z := by
    apply ha
    change a * v.val (n + 1) = a * (a ^ n * z)
    simpa [pow_succ', mul_assoc] using hz
  have hvmem : v.val (n + 1) ∈ (Ideal.span {a}) ^ n := by
    rw [hv, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hdelta := v.property (Nat.le_succ n)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdelta
  have hn : v.val n ∈ (Ideal.span {a}) ^ n := by
    simpa using (Ideal.span {a} ^ n).add_mem hdelta hvmem
  simpa only [AdicCompletion.evalₐ_mk, map_zero] using
    Ideal.Quotient.eq_zero_iff_mem.mpr hn

end AdicCompletionRegular

section AdicCompletionChangeIdeal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- J進完備化がI進完備なら、元の加群の像を保つI進完備化からの自然な写像。 -/
def adicCompletionChangeIdealMap (I J : Ideal R) [IsAdicComplete I (AdicCompletion J M)] :
    AdicCompletion I M →ₗ[R] AdicCompletion J M :=
  (AdicCompletion.ofLinearEquiv I (AdicCompletion J M)).symm.toLinearMap.comp
    ((AdicCompletion.map I (AdicCompletion.of J M)).restrictScalars R)

@[simp] theorem adicCompletionChangeIdealMap_of (I J : Ideal R)
    [IsAdicComplete I (AdicCompletion J M)] (m : M) :
    adicCompletionChangeIdealMap I J (AdicCompletion.of I M m) = AdicCompletion.of J M m := by
  change (AdicCompletion.ofLinearEquiv I (AdicCompletion J M)).symm
    (AdicCompletion.map I (AdicCompletion.of J M) (AdicCompletion.of I M m)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]

/-- 互いのイデアルについて完備な二つの完備化を、元の加群の像を保って同定する。 -/
def adicCompletionChangeIdealEquiv (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    [IsAdicComplete I (AdicCompletion J M)] [IsAdicComplete J (AdicCompletion I M)] :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M := by
  let : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  let : IsAdicComplete J (AdicCompletion J M) := AdicCompletion.isAdicComplete hJ
  let f := adicCompletionChangeIdealMap (M := M) I J
  let g := adicCompletionChangeIdealMap (M := M) J I
  have hfg : f.comp g = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of J hJ
    ext m
    simp [f, g]
  have hgf : g.comp f = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of I hI
    ext m
    simp [f, g]
  exact LinearEquiv.ofLinearMap f g hfg hgf

@[simp] theorem adicCompletionChangeIdealEquiv_of (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    [IsAdicComplete I (AdicCompletion J M)] [IsAdicComplete J (AdicCompletion I M)] (m : M) :
    adicCompletionChangeIdealEquiv I J hI hJ (AdicCompletion.of I M m) =
      AdicCompletion.of J M m :=
  adicCompletionChangeIdealMap_of I J m

end AdicCompletionChangeIdeal

end SerrePositivity
