module

public import SerrePositivity.CommutativeAlgebra.Idempotent
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.AbsolutelyIntegrallyClosedQuotient
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.CompatibleRootPerfectoid
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs

/-! # perfectoid 環の冪等元による直因子と有限直積の perfectoid 化

## 概要

perfectoid 環を冪等元で割った直因子は perfectoid である（`isIntegralPerfectoid_idempotent_quotient`）。指定した有限直積の perfectoid 化について、各射影の核の像による商で成分の普遍単位を作り（`productPerfectoidComponent`・`productComponentUnit`）、成分の単位の直積との同型を構成して直積の単位の普遍性を示す。
BS 著者版 Corollary 7.3 の普遍性を、冪等元による直因子と有限直積に適用する。

## 方針

冪等元を定数の両立する p 冪根の族と見て、根族の完備な商の定理を当てる。商の完備性は補冪等元の零化商の API から得る。

## 規約

絶対整閉性や一般の integral perfectoid 化の存在の引用は使わない。全体の普遍単位は指定したデータとして保つ。旧 `CLMST/Prop247IdempotentQuotient`・`Prop247ProductComponents`・`Prop247ProductUniversality`（`prop247_` を外した。CLMST Prop 2.4.7 の階数ごとの分解の perfectoid 化）。

## 使われ方

CLMST の `PerfectoidizationIsogeny`（Prop 2.4.7）の階数の積の普遍性。
-/

@[expose] public noncomputable section

universe u

section IdempotentQuotientPart

namespace SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false

/-- 任意の perfectoid 環の冪等元による商は perfectoid である。零環も含む。 -/
theorem Semiperfectoid.isIntegralPerfectoid_idempotent_quotient
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (e : R) (he : IsIdempotentElem e) :
    _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ Ideal.span {e}) p := by
  letI := hR.isAdicComplete R p
  have hc := _root_.SerrePositivity.BhattScholze.Semiperfectoid.annihilatorPrincipalQuotient_isAdicComplete R p (1 - e)
  rw [_root_.SerrePositivity.annihilator_span_one_sub_of_idempotent R e he] at hc
  letI := hc
  let ρ : R → ℕ → R := fun _ _ => e
  have hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n := fun _ _ =>
    he.pow_eq (Fact.out : p.Prime).ne_zero
  have hK : SerrePositivity.compatibleRootFamilyIdeal ρ = Ideal.span {e} := by
    simp only [SerrePositivity.compatibleRootFamilyIdeal, ρ, Set.range_const]
  have hP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  change _root_.SerrePositivity.IsIntegralPerfectoid
    (AdicCompletion (Ideal.span {(p : R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)})
      (R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)) p at hP
  rw [hK] at hP
  let eqv : (R ⧸ Ideal.span {e}) ≃+*
      AdicCompletion (Ideal.span {(p : R ⧸ Ideal.span {e})}) (R ⧸ Ideal.span {e}) :=
    RingEquiv.ofBijective (algebraMap _ _) (by
      change Function.Bijective (AdicCompletion.of _ _)
      exact AdicCompletion.of_bijective _ _)
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p eqv.symm hP

end SerrePositivity.BhattScholze

end IdempotentQuotientPart

section ProductComponentsPart

namespace SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Finite ι] (A : ι → Type u) [∀ i, CommRing (A i)]
    (C : Type u) [CommRing C] (f : ((i : ι) → A i) →+* C)

/-- 全体の指定終域の、元の射影の核の像による実商。 -/
abbrev Semiperfectoid.productPerfectoidComponent (i : ι) : Type u :=
  C ⧸ (RingHom.ker (Pi.evalRingHom A i)).map f

/-- 元の成分から元の実商への標準単位。 -/
def Semiperfectoid.productComponentUnit (i : ι) : A i →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidComponent A C f i :=
  (Ideal.quotientMap ((RingHom.ker (Pi.evalRingHom A i)).map f) f Ideal.le_comap_map).comp
    ((Pi.evalRingHom A i).quotientKerEquivOfSurjective (Function.surjective_eval i)).symm.toRingHom

/-- 元の単位は元の射影と商写像に関して可換である。 -/
theorem Semiperfectoid.productComponentUnit_comp_eval (i : ι) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit A C f i).comp (Pi.evalRingHom A i) =
      (Ideal.Quotient.mk ((RingHom.ker (Pi.evalRingHom A i)).map f)).comp f := by
  unfold _root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit
  rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
  rfl

/-- 指定した積の perfectoid 化の各実成分は perfectoid である。 -/
theorem Semiperfectoid.productPerfectoidComponent_isIntegralPerfectoid
    (p : ℕ) [Fact p.Prime] (hf : _root_.SerrePositivity.IsPerfectoidization p f) (i : ι) :
    _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidComponent A C f i) p := by
  classical
  letI := Fintype.ofFinite ι
  have he := (((CompleteOrthogonalIdempotents.single A).idem i).map f).one_sub
  change _root_.SerrePositivity.IsIntegralPerfectoid (C ⧸ (RingHom.ker (Pi.evalRingHom A i)).map f) p
  rw [_root_.SerrePositivity.map_ker_pi_eval_eq_span A f i]
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.isIntegralPerfectoid_idempotent_quotient C p hf.1 _ he

/-- 各元の実商への単位は、元の Ai の perfectoid 化である。 -/
theorem Semiperfectoid.productComponentUnit_isPerfectoidization
    (p : ℕ) [Fact p.Prime] (hf : _root_.SerrePositivity.IsPerfectoidization p f) (i : ι) :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit A C f i) := by
  let D := _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidComponent A C f i
  have hD := _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidComponent_isIntegralPerfectoid A C f p hf i
  have hq := hf.quotient_map (RingHom.ker (Pi.evalRingHom A i)) (RingHom.id D)
    hD.isPerfectoidization_id
  have h := hq.precomp_ringEquiv
    ((Pi.evalRingHom A i).quotientKerEquivOfSurjective (Function.surjective_eval i)).symm
  dsimp only [D] at h
  simpa only [RingHom.id_comp, _root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit] using h

end SerrePositivity.BhattScholze

end ProductComponentsPart

section ProductUniversalityPart

namespace SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Finite ι] (A P : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (P i)] (β : ∀ i, A i →+* P i)

/-- 元の各成分単位を元の各射影と合成した直積。 -/
def Semiperfectoid.productPerfectoidizationUnit : ((i : ι) → A i) →+* ((i : ι) → P i) :=
  RingHom.pi (fun i => (β i).comp (Pi.evalRingHom A i))

variable (p : ℕ) [Fact p.Prime] (hβ : ∀ i, IsPerfectoidization p (β i))
    (C : Type u) [CommRing C] (f : ((i : ι) → A i) →+* C) (hf : IsPerfectoidization p f)

include hβ hf

/-- 指定した全体の普遍単位は、元の成分単位の直積へ元の写像を保つ同型を持つ。 -/
theorem Semiperfectoid.productPerfectoidization_exists_equiv :
    ∃ e : C ≃+* ((i : ι) → P i),
      e.toRingHom.comp f = _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit A P β := by
  classical
  let D := fun i => _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidComponent A C f i
  choose ε hε using fun i => (hβ i).exists_equiv p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit_isPerfectoidization A C f p hf i)
  let eC : C ≃+* ((i : ι) → D i) := RingEquiv.ofBijective
    (RingHom.pi (fun i => Ideal.Quotient.mk ((RingHom.ker (Pi.evalRingHom A i)).map f)))
    (_root_.SerrePositivity.pi_mapped_projection_quotients_bijective A f)
  let eP : ((i : ι) → P i) ≃+* ((i : ι) → D i) := RingEquiv.piCongrRight ε
  let e := eC.trans eP.symm
  refine ⟨e, ?_⟩
  apply RingHom.ext
  intro x
  funext i
  apply (ε i).injective
  change ε i ((eP.symm (eC (f x))) i) = ε i (β i (x i))
  calc
    ε i ((eP.symm (eC (f x))) i) = (eC (f x)) i :=
      congrFun (eP.apply_symm_apply (eC (f x))) i
    _ = _root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit A C f i (x i) :=
      (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productComponentUnit_comp_eval A C f i) x).symm
    _ = ε i (β i (x i)) := (RingHom.congr_fun (hε i) (x i)).symm

/-- 元の成分単位の直積は perfectoid 化である。
全体の普遍単位を指定データとして受け取り、存在の引用は使わない。 -/
theorem Semiperfectoid.productUnit_isPerfectoidization_of_specified :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit A P β) := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidization_exists_equiv A P β p hβ C f hf
  refine ⟨_root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p e hf.1, ?_⟩
  intro U _ hU k
  obtain ⟨l, hl, hu⟩ := hf.2 U hU k
  refine ⟨l.comp e.symm.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l (e.symm (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit A P β x)) = k x
    have hx := RingHom.congr_fun he x
    change e (f x) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit A P β x at hx
    rw [← hx, e.symm_apply_apply]
    exact RingHom.congr_fun hl x
  · intro m hm
    have hm' : (m.comp e.toRingHom).comp f = k := by
      apply RingHom.ext
      intro x
      change m (e (f x)) = k x
      have hx := RingHom.congr_fun he x
      change e (f x) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit A P β x at hx
      rw [hx]
      exact RingHom.congr_fun hm x
    have H := hu (m.comp e.toRingHom) hm'
    apply RingHom.ext
    intro y
    change m y = l (e.symm y)
    have h := RingHom.congr_fun H (e.symm y)
    change m (e (e.symm y)) = l (e.symm y) at h
    simpa only [e.apply_symm_apply] using h

end SerrePositivity.BhattScholze

end ProductUniversalityPart
