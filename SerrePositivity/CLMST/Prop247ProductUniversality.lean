module

public import SerrePositivity.CLMST.Prop247ProductComponents
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness

/-! # Prop 2.4.7：有限直積の元の普遍単位

指定した全体の普遍単位を、各射影の核による実商と既存の冪等元分解で成分へ移す。
元の成分単位の直積との同型を構成し、その直積単位の普遍性を証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Finite ι] (A P : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (P i)] (β : ∀ i, A i →+* P i)

/-- 元の各成分単位を元の各射影と合成した直積。 -/
def prop247_productPerfectoidizationUnit : ((i : ι) → A i) →+* ((i : ι) → P i) :=
  RingHom.pi (fun i => (β i).comp (Pi.evalRingHom A i))

variable (p : ℕ) [Fact p.Prime] (hβ : ∀ i, IsPerfectoidization p (β i))
    (C : Type u) [CommRing C] (f : ((i : ι) → A i) →+* C) (hf : IsPerfectoidization p f)

include hβ hf

/-- 指定した全体の普遍単位は、元の成分単位の直積へ元の写像を保つ同型を持つ。 -/
theorem prop247_productPerfectoidization_exists_equiv :
    ∃ e : C ≃+* ((i : ι) → P i),
      e.toRingHom.comp f = prop247_productPerfectoidizationUnit A P β := by
  classical
  let D := fun i => prop247_productPerfectoidComponent A C f i
  choose ε hε using fun i => (hβ i).exists_equiv p
    (prop247_productComponentUnit_isPerfectoidization A C f p hf i)
  let eC : C ≃+* ((i : ι) → D i) := RingEquiv.ofBijective
    (RingHom.pi (fun i => Ideal.Quotient.mk ((RingHom.ker (Pi.evalRingHom A i)).map f)))
    (pi_mapped_projection_quotients_bijective A f)
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
    _ = prop247_productComponentUnit A C f i (x i) :=
      (RingHom.congr_fun (prop247_productComponentUnit_comp_eval A C f i) x).symm
    _ = ε i (β i (x i)) := (RingHom.congr_fun (hε i) (x i)).symm

/-- 元の成分単位の直積は perfectoid 化である。
全体の普遍単位を指定データとして受け取り、存在の引用は使わない。 -/
theorem prop247_productUnit_isPerfectoidization_of_specified :
    IsPerfectoidization p (prop247_productPerfectoidizationUnit A P β) := by
  obtain ⟨e, he⟩ := prop247_productPerfectoidization_exists_equiv A P β p hβ C f hf
  refine ⟨BhattScholze.isIntegralPerfectoid_of_ringEquiv p e hf.1, ?_⟩
  intro U _ hU k
  obtain ⟨l, hl, hu⟩ := hf.2 U hU k
  refine ⟨l.comp e.symm.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l (e.symm (prop247_productPerfectoidizationUnit A P β x)) = k x
    have hx := RingHom.congr_fun he x
    change e (f x) = prop247_productPerfectoidizationUnit A P β x at hx
    rw [← hx, e.symm_apply_apply]
    exact RingHom.congr_fun hl x
  · intro m hm
    have hm' : (m.comp e.toRingHom).comp f = k := by
      apply RingHom.ext
      intro x
      change m (e (f x)) = k x
      have hx := RingHom.congr_fun he x
      change e (f x) = prop247_productPerfectoidizationUnit A P β x at hx
      rw [hx]
      exact RingHom.congr_fun hm x
    have H := hu (m.comp e.toRingHom) hm'
    apply RingHom.ext
    intro y
    change m y = l (e.symm y)
    have h := RingHom.congr_fun H (e.symm y)
    change m (e (e.symm y)) = l (e.symm y) at h
    simpa only [e.apply_symm_apply] using h

end SerrePositivity.CLMST
