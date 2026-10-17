module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationIdentity
public import SerrePositivity.BhattScholze.PerfectoidRingEquiv

/-! # Prop 2.4.7：異なる perfectoid 対象の有限直積の指定普遍単位

各成分が異なる場合にも、指定した普遍単位は元の代数同型である。
普遍対象の存在を引用せず、指定された元の写像の普遍性を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 各成分が perfectoid な有限直積の、指定した perfectoid 化単位は元の代数同型である。
成分環が全て同じ環であることは要求しない。 -/
theorem prop247_product_unit_exists_algEquiv
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    {ι : Type u} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : ((i : ι) → T i) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ e : ((i : ι) → T i) ≃ₐ[R] C, e.toAlgHom = f := by
  let k : C →ₐ[R] (i : ι) → T i := AlgHom.pi (fun i =>
    IsPerfectoidization.mapAlgHom hf
      (show IsPerfectoidization p (AlgHom.id R (T i)).toRingHom from
        (hT i).isPerfectoidization_id)
      (Pi.evalAlgHom R T i))
  have hkf : k.comp f = AlgHom.id R ((i : ι) → T i) := by
    ext x i
    exact AlgHom.congr_fun (IsPerfectoidization.mapAlgHom_comp hf
      (show IsPerfectoidization p (AlgHom.id R (T i)).toRingHom from
        (hT i).isPerfectoidization_id) (Pi.evalAlgHom R T i)) x
  have hkf' : k.toRingHom.comp f.toRingHom = RingHom.id ((i : ι) → T i) :=
    congrArg AlgHom.toRingHom hkf
  have hfk : f.toRingHom.comp k.toRingHom = RingHom.id C := by
    obtain ⟨a, _ha, hu⟩ := hf.2 C hf.1 f.toRingHom
    exact (hu (f.toRingHom.comp k.toRingHom) (by
      change (f.toRingHom.comp k.toRingHom).comp f.toRingHom = f.toRingHom
      rw [RingHom.comp_assoc, hkf', RingHom.comp_id])).trans
      (hu (RingHom.id C) (RingHom.id_comp f.toRingHom)).symm
  let e : ((i : ι) → T i) ≃ₐ[R] C :=
    { f with invFun := k
             left_inv := fun x => AlgHom.congr_fun hkf x
             right_inv := fun x => RingHom.congr_fun hfk x }
  exact ⟨e, rfl⟩

/-- 指定した普遍単位を持つこの有限直積は perfectoid である。
存在の追加仮定を隠さず、前の元の単位の同型を使う。 -/
theorem prop247_product_perfectoid_of_specified_unit
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    {ι : Type u} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : ((i : ι) → T i) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    IsIntegralPerfectoid ((i : ι) → T i) p := by
  obtain ⟨e, _he⟩ := prop247_product_unit_exists_algEquiv R p T hT C f hf
  exact BhattScholze.isIntegralPerfectoid_of_ringEquiv p e.symm.toRingEquiv hf.1

end SerrePositivity.CLMST
