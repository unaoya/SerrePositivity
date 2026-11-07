module

public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

@[expose] public section

universe u

namespace SerrePositivity

section LinearOrder

variable {α : Type u} [LinearOrder α]

/-- BM18 Lemma 4.7 の順序論部分。左端を固定し、良い右端の集合に Zorn の補題を使う。
(1) は退化区間に用いる。上限が達成されていない場合は (4) と (5) で上限を含める。 -/
theorem intervalProperty_of_localExtensions
    (hsup : ∀ s : Set α, s.Nonempty → ∃ b, IsLUB s b)
    (P : α → α → Prop)
    (hpoint : ∀ a, P a a)
    (hsub : ∀ {a b c d}, P a b → a ≤ c → c ≤ d → d ≤ b → P c d)
    (hright : ∀ {a b}, a < b → ∃ c, a < c ∧ P a c)
    (hleft : ∀ {a b}, a < b → ∃ c, c < b ∧ P c b)
    (hglue : ∀ {a b c d}, a ≤ c → c ≤ b → b ≤ d → P a b → P c d → P a d)
    {a b : α} (hab : a ≤ b) : P a b := by
  let S : Set α := {q | a ≤ q ∧ P a q}
  have hupper (T : Set α) (hTS : T ⊆ S) (y : α) (hy : y ∈ T) :
      ∃ q ∈ S, ∀ z ∈ T, z ≤ q := by
    obtain ⟨q, hq⟩ := hsup T ⟨y, hy⟩
    have haq : a ≤ q := (hTS hy).1.trans (hq.1 hy)
    refine ⟨q, ⟨haq, ?_⟩, fun z hz => hq.1 hz⟩
    by_cases hqT : q ∈ T
    · exact (hTS hqT).2
    · have haq' : a < q := lt_of_le_of_ne haq (by
        intro he
        exact hqT (le_antisymm (hq.1 hy) (he ▸ (hTS hy).1) ▸ hy))
      obtain ⟨c, hcq, hc⟩ := hleft haq'
      let r := max a c
      have hrq : r < q := max_lt haq' hcq
      have hr : P r q := hsub hc (le_max_right _ _) hrq.le le_rfl
      have hrt : ∃ t ∈ T, r < t := by
        by_contra! h
        exact hrq.not_ge (hq.2 h)
      obtain ⟨t, ht, hrt⟩ := hrt
      exact hglue (le_max_left _ _) hrt.le (hq.1 ht) (hTS ht).2 hr
  obtain ⟨m, ham, hm⟩ := zorn_le_nonempty₀ S (fun T hTS _ => hupper T hTS) a
    ⟨le_rfl, hpoint a⟩
  by_cases hmb : b ≤ m
  · exact hsub hm.1.2 le_rfl hab hmb
  · obtain ⟨c, hmc, hc⟩ := hright (lt_of_not_ge hmb)
    have hcS : c ∈ S := ⟨ham.trans hmc.le, hglue ham le_rfl hmc.le hm.1.2 hc⟩
    exact (not_le_of_gt hmc (hm.le_of_ge hcS hmc.le)).elim

end LinearOrder

section Valuation

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- 付値環の空でない素イデアル族の合併は素イデアル。 -/
theorem primeSpectrum_asIdeal_sSup_isPrime (s : Set (PrimeSpectrum V)) (hs : s.Nonempty) :
    (sSup (PrimeSpectrum.asIdeal '' s)).IsPrime := by
  classical
  let t := PrimeSpectrum.asIdeal '' s
  have ht : t.Nonempty := hs.image _
  have hd : DirectedOn (· ≤ ·) t := fun a ha b hb =>
    (le_total a b).elim (fun h => ⟨b, hb, h, le_rfl⟩) (fun h => ⟨a, ha, le_rfl, h⟩)
  have hmem {x : V} : x ∈ sSup t ↔ ∃ I ∈ t, x ∈ I :=
    Submodule.mem_sSup_of_directed ht hd
  change (sSup t).IsPrime
  refine ⟨?_, ?_⟩
  · intro he
    obtain ⟨I, ⟨q, hq, rfl⟩, hI⟩ := hmem.mp (show (1 : V) ∈ sSup t by simp [he])
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hI isUnit_one)
  · intro x y hxy
    obtain ⟨I, ⟨q, hq, rfl⟩, hI⟩ := hmem.mp hxy
    exact (q.isPrime.mem_or_mem hI).imp (fun hx => hmem.mpr ⟨_, ⟨q, hq, rfl⟩, hx⟩)
      (fun hy => hmem.mpr ⟨_, ⟨q, hq, rfl⟩, hy⟩)

private theorem primeSpectrum_isLUB (s : Set (PrimeSpectrum V)) (hs : s.Nonempty) :
    ∃ b, IsLUB s b := by
  let t := PrimeSpectrum.asIdeal '' s
  have hprime := primeSpectrum_asIdeal_sSup_isPrime s hs
  let q : PrimeSpectrum V := ⟨sSup t, hprime⟩
  refine ⟨q, ?_, ?_⟩
  · intro x hx
    change x.asIdeal ≤ sSup t
    exact le_sSup (show x.asIdeal ∈ t from ⟨x, hx, rfl⟩)
  · intro x hx
    change sSup t ≤ x.asIdeal
    apply sSup_le
    rintro _ ⟨z, hz, rfl⟩
    exact hx hz

/-- 付値環のスペクトルの区間についての判定（BM18 Lemma 4.7）。
区間は下端と上端で表し、重なる区間の貼り合わせは端点の不等式で表す。 -/
theorem valuationIntervalProperty_of_localExtensions
    (P : PrimeSpectrum V → PrimeSpectrum V → Prop)
    (hpoint : ∀ a, P a a)
    (hsub : ∀ {a b c d}, P a b → a ≤ c → c ≤ d → d ≤ b → P c d)
    (hright : ∀ {a b}, a < b → ∃ c, a < c ∧ P a c)
    (hleft : ∀ {a b}, a < b → ∃ c, c < b ∧ P c b)
    (hglue : ∀ {a b c d}, a ≤ c → c ≤ b → b ≤ d → P a b → P c d → P a d)
    {a b : PrimeSpectrum V} (hab : a ≤ b) : P a b := by
  classical
  let : LinearOrder (PrimeSpectrum V) :=
    LinearOrder.lift' PrimeSpectrum.asIdeal (fun _ _ h => PrimeSpectrum.ext h)
  exact intervalProperty_of_localExtensions primeSpectrum_isLUB P hpoint hsub hright hleft hglue hab

end Valuation

end SerrePositivity
