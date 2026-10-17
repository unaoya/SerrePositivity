module

public import SerrePositivity.CommutativeAlgebra.ProductIdempotentQuotient
public import SerrePositivity.CLMST.Prop247IdempotentQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationIdentity

/-! # Prop 2.4.7：指定した積の perfectoid 化の実成分

元の各射影の核の像による商を取り、元の各成分の普遍単位を構成する。
一般 integral 存在の入力は使わず、全体の普遍単位を指定データとして保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Finite ι] (A : ι → Type u) [∀ i, CommRing (A i)]
    (C : Type u) [CommRing C] (f : ((i : ι) → A i) →+* C)

/-- 全体の指定終域の、元の射影の核の像による実商。 -/
abbrev prop247_productPerfectoidComponent (i : ι) : Type u :=
  C ⧸ (RingHom.ker (Pi.evalRingHom A i)).map f

/-- 元の成分から元の実商への標準単位。 -/
def prop247_productComponentUnit (i : ι) : A i →+* prop247_productPerfectoidComponent A C f i :=
  (Ideal.quotientMap ((RingHom.ker (Pi.evalRingHom A i)).map f) f Ideal.le_comap_map).comp
    ((Pi.evalRingHom A i).quotientKerEquivOfSurjective (Function.surjective_eval i)).symm.toRingHom

/-- 元の単位は元の射影と商写像に関して可換である。 -/
theorem prop247_productComponentUnit_comp_eval (i : ι) :
    (prop247_productComponentUnit A C f i).comp (Pi.evalRingHom A i) =
      (Ideal.Quotient.mk ((RingHom.ker (Pi.evalRingHom A i)).map f)).comp f := by
  unfold prop247_productComponentUnit
  rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
  rfl

/-- 指定した積の perfectoid 化の各実成分は perfectoid である。 -/
theorem prop247_productPerfectoidComponent_isIntegralPerfectoid
    (p : ℕ) [Fact p.Prime] (hf : IsPerfectoidization p f) (i : ι) :
    IsIntegralPerfectoid (prop247_productPerfectoidComponent A C f i) p := by
  classical
  letI := Fintype.ofFinite ι
  have he := (((CompleteOrthogonalIdempotents.single A).idem i).map f).one_sub
  change IsIntegralPerfectoid (C ⧸ (RingHom.ker (Pi.evalRingHom A i)).map f) p
  rw [map_ker_pi_eval_eq_span A f i]
  exact prop247_isIntegralPerfectoid_idempotent_quotient C p hf.1 _ he

/-- 各元の実商への単位は、元の Ai の perfectoid 化である。 -/
theorem prop247_productComponentUnit_isPerfectoidization
    (p : ℕ) [Fact p.Prime] (hf : IsPerfectoidization p f) (i : ι) :
    IsPerfectoidization p (prop247_productComponentUnit A C f i) := by
  let D := prop247_productPerfectoidComponent A C f i
  have hD := prop247_productPerfectoidComponent_isIntegralPerfectoid A C f p hf i
  have hq := hf.quotient_map (RingHom.ker (Pi.evalRingHom A i)) (RingHom.id D)
    hD.isPerfectoidization_id
  have h := hq.precomp_ringEquiv
    ((Pi.evalRingHom A i).quotientKerEquivOfSurjective (Function.surjective_eval i)).symm
  dsimp only [D] at h
  simpa only [RingHom.id_comp, prop247_productComponentUnit] using h

end SerrePositivity.CLMST
