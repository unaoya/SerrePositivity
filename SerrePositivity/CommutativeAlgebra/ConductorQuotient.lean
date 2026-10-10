module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# 共通分母による商への写像の核の消滅

環の包含 `B → C` と `g ∈ B` が `gC ⊆ B` を満たすなら、任意のイデアル `I ⊆ B` について
`B/I → C/IC` の核は `g` で消える。Noether 性や長さの有限性は不要。
定理2.5のトレースから得られる共通分母に適用するための一般論。
-/

public section
universe u
namespace SerrePositivity

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- `gC ⊆ B` なら、拡大したイデアル `IC` の元に `g` を掛けると `I` から来る。 -/
theorem exists_mul_lift_of_conductor (I : Ideal B) (g : B)
    (hg : ∀ c : C, ∃ b : B, algebraMap B C b = algebraMap B C g * c)
    {x : C} (hx : x ∈ I.map (algebraMap B C)) :
    ∃ b ∈ I, algebraMap B C b = algebraMap B C g * x := by
  have h : ∀ {x : C}, x ∈ I.map (algebraMap B C) →
      ∀ c : C, ∃ b ∈ I, algebraMap B C b = algebraMap B C g * (c * x) := by
    intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        intro c
        obtain ⟨b, hb⟩ := hg c
        exact ⟨b * a, I.mul_mem_left b ha, by rw [map_mul, hb, mul_assoc]⟩
    | zero =>
        intro c
        exact ⟨0, I.zero_mem, by simp⟩
    | add x y hx hy ihx ihy =>
        intro c
        obtain ⟨a, ha, hea⟩ := ihx c
        obtain ⟨b, hb, heb⟩ := ihy c
        exact ⟨a + b, I.add_mem ha hb, by rw [map_add, hea, heb, mul_add, mul_add]⟩
    | smul r x hx ih =>
        intro c
        simpa only [smul_eq_mul, mul_assoc] using ih (c * r)
  simpa only [one_mul] using h hx 1

/-- 単射な環拡大では、拡大イデアルの逆像に属する元を共通分母が元のイデアルへ送る。 -/
theorem mul_mem_of_mem_map_of_conductor
    (hinj : Function.Injective (algebraMap B C)) (I : Ideal B) (g : B)
    (hg : ∀ c : C, ∃ b : B, algebraMap B C b = algebraMap B C g * c)
    {x : B} (hx : algebraMap B C x ∈ I.map (algebraMap B C)) : g * x ∈ I := by
  obtain ⟨b, hb, heq⟩ := exists_mul_lift_of_conductor I g hg hx
  rw [← map_mul] at heq
  exact hinj heq ▸ hb

/-- 拡大イデアルへの商写像。包含の仮定を要さず任意の代数で定義できる。 -/
noncomputable def quotientToExtension (I : Ideal B) :
    B ⧸ I →ₐ[B] C ⧸ I.map (algebraMap B C) :=
  Ideal.quotientMapₐ _ (Algebra.ofId B C) Ideal.le_comap_map

/-- 商写像は代表元を係数拡大の構造写像で送る。 -/
@[simp] theorem quotientToExtension_mk (I : Ideal B) (b : B) :
    quotientToExtension (C := C) I (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap B C)) (algebraMap B C b) := by
  rfl

/-- 共通分母は `B/I → C/IC` の核を消す。 -/
theorem smul_eq_zero_of_quotientToExtension_eq_zero
    (hinj : Function.Injective (algebraMap B C)) (I : Ideal B) (g : B)
    (hg : ∀ c : C, ∃ b : B, algebraMap B C b = algebraMap B C g * c)
    (x : B ⧸ I) (hx : quotientToExtension (C := C) I x = 0) : g • x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (algebraMap B C x) = 0 at hx
  have hm := mul_mem_of_mem_map_of_conductor hinj I g hg
    (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  change Ideal.Quotient.mk I (g * x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hm

/-- 商加群上の `g` 倍写像の余核は、イデアルに `g` を加えた商である。
係数環 `R` 上の線形同型として構成し、係数制限した長さにも使える形にする。 -/
noncomputable def quotientSmulCokerEquiv (R : Type u) [CommRing R] [Algebra R B]
    (I : Ideal B) (g : B) :
    ((B ⧸ I) ⧸ LinearMap.range ((LinearMap.lsmul B (B ⧸ I) g).restrictScalars R)) ≃ₗ[R]
      B ⧸ (I ⊔ Ideal.span {g}) := by
  let f : (B ⧸ I) →ₗ[R] B ⧸ (I ⊔ Ideal.span {g}) :=
    (Ideal.Quotient.factorₐ R le_sup_left).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective le_sup_left
  have hk : LinearMap.range ((LinearMap.lsmul B (B ⧸ I) g).restrictScalars R) =
      LinearMap.ker f := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk I (g * y) = Ideal.Quotient.mk I x at hy
      rw [← hy]
      change Ideal.Quotient.mk (I ⊔ Ideal.span {g}) (g * y) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (show Ideal.span {g} ≤ I ⊔ Ideal.span {g} from le_sup_right)
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton g)))
    · intro hx
      change Ideal.Quotient.mk (I ⊔ Ideal.span {g}) x = 0 at hx
      have hx' := Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [sup_comm, Ideal.mem_span_singleton_sup] at hx'
      obtain ⟨a, b, hb, rfl⟩ := hx'
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      change Ideal.Quotient.mk I (g * a) = Ideal.Quotient.mk I (a * g + b)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, mul_comm]
  exact (Submodule.quotEquivOfEq _ _ hk).trans (LinearMap.quotKerEquivOfSurjective f hf)

end SerrePositivity
