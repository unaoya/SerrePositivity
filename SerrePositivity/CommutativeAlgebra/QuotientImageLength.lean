module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Length

/-! # 全射環準同型による商の長さの移送

核を含むイデアルで割ると、全射の像の商と同型になり、それぞれの環に関する長さが等しい。
共通の基底環に関する線形性は仮定しない。Frobeniusでねじれた比較にも使える。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R S : Type*} [CommRing R] [CommRing S]

/-- 核を含むイデアルによる商と、その全射像による商の同型。 -/
def quotientImageEquiv (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) : R ⧸ I ≃+* S ⧸ I.map f := by
  have heq : I = (I.map f).comap f := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  exact RingEquiv.ofBijective (Ideal.quotientMap (I.map f) f heq.le)
    ⟨Ideal.quotientMap_injective' heq.ge, Ideal.quotientMap_surjective hf⟩

@[simp] theorem quotientImageEquiv_mk (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) (a : R) :
    quotientImageEquiv f hf I hker (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map f) (f a) := rfl

/-- 長さは全射環準同型と商同型を通じて移せる。 -/
theorem length_quotient_eq_image_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map f) := by
  let e := quotientImageEquiv f hf I hker
  let g : R ⧸ I →ₛₗ[f] S ⧸ I.map f :=
    { e.toAddEquiv.toAddMonoidHom with
      map_smul' := by
        intro r a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change e (Ideal.Quotient.mk I (r * a)) =
          Ideal.Quotient.mk (I.map f) (f r * f a)
        exact congrArg (Ideal.Quotient.mk (I.map f)) (f.map_mul r a) }
  let : RingHomSurjective f := ⟨hf⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective g e.bijective)]

end SerrePositivity
