module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # 完全環の Perfection と反復 Frobenius の核

## 概要

標数 p で Frobenius が全射な環で、最初の核の生成元の両立する根から反復 Frobenius の核の生成元を得る（`ker_iterateFrobenius_eq_span`）。成分ごとの割り算やイデアル内の誤差の補正から Perfection の第 0 射影の核を生成し、Frobenius で根を取れる核を持つ全射の Perfection は全射で核も持ち上がる。完全標数 p 環では単項イデアルの零化イデアルが p 乗根を持ち、任意の単項イデアル商の Perfection の射影核を計算する。正則元 r の冪 r^N による商で r を零化する元は r^(N-1) の倍数である。

## 方針

根を一段先で選んで p 乗し、隣接成分の誤差を消して両立する列を作る。Noether 性・被約性・perfectoid 性は仮定しない。

## 規約

p 冪写像の全単射性と標準的な p 冪根は Mathlib の `bijective_iterateFrobenius`・`frobeniusEquiv` の逆の反復と `iterate_frobeniusEquiv_symm_pow_p_pow` を直接使う。`principalAnnihilator` は `(Ideal.span {a}).annihilator` に置き換える候補。`ker_iterateFrobenius_eq_span` は残す。

## 使われ方

BhattScholze の perfect prism と perfectoid 化の核、`Perfectoid/Fontaine`（商の零化元は Fontaine 核の生成元の判定に使う）。
-/

@[expose] public noncomputable section

universe u

section FrobeniusRootKernelsPart

namespace SerrePositivity

/-- 互換的な p 乗根の列の、任意の二段の間の冪関係。 -/
theorem compatibleRoots_pow
    {R : Type u} [Monoid R] (p : ℕ) (e : ℕ → R)
    (he : ∀ n, e (n + 1) ^ p = e n) (m n : ℕ) :
    e (m + n) ^ (p ^ n) = e m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← Nat.add_assoc, he, ih]

/-- 互換的な根の生成する主イデアルは段を進めると大きくなる。 -/
theorem span_compatibleRoot_le_succ
    {R : Type u} [CommSemiring R] (p : ℕ) (hp : p ≠ 0) (e : ℕ → R)
    (he : ∀ n, e (n + 1) ^ p = e n) (n : ℕ) :
    Ideal.span {e n} ≤ Ideal.span {e (n + 1)} := by
  rw [Ideal.span_singleton_le_span_singleton, ← he n]
  exact dvd_pow_self _ hp

/-- 最初の核と互換的な根の列から、反復 Frobenius の核を計算する。 -/
theorem frobenius_pow_kernel_iff_mem_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : Function.Surjective (frobenius R p)) (e : ℕ → R)
    (he0 : e 0 = 0) (he : ∀ n, e (n + 1) ^ p = e n)
    (hker : ∀ x : R, x ^ p = 0 ↔ x ∈ Ideal.span {e 1})
    (n : ℕ) (x : R) : x ^ (p ^ n) = 0 ↔ x ∈ Ideal.span {e n} := by
  induction n generalizing x with
  | zero => simp [he0]
  | succ n ih =>
    constructor
    · intro hx
      have hxp : (x ^ (p ^ n)) ^ p = 0 := by
        rw [← pow_mul, ← pow_succ]
        exact hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp ((hker _).mp hxp)
      obtain ⟨b, hb⟩ := hF.iterate n a
      rw [iterate_frobenius] at hb
      have hdiff : (x - e (n + 1) * b) ^ (p ^ n) = 0 := by
        rw [sub_pow_char_pow, mul_pow]
        have hroot : e (n + 1) ^ (p ^ n) = e 1 := by
          simpa only [Nat.add_comm] using compatibleRoots_pow p e he 1 n
        rw [hroot, hb, ← ha, sub_self]
      have hmem : x - e (n + 1) * b ∈ Ideal.span {e (n + 1)} :=
        span_compatibleRoot_le_succ p (Fact.out : p.Prime).ne_zero e he n
          ((ih _).mp hdiff)
      have hprod : e (n + 1) * b ∈ Ideal.span {e (n + 1)} :=
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      simpa only [sub_add_cancel] using (Ideal.span {e (n + 1)}).add_mem hmem hprod
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
      have hen : e (n + 1) ^ (p ^ (n + 1)) = 0 := by
        simpa only [Nat.zero_add, he0] using compatibleRoots_pow p e he 0 (n + 1)
      rw [mul_pow, hen, zero_mul]

/-- 理想としての反復 Frobenius の核の計算。 -/
theorem ker_iterateFrobenius_eq_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : Function.Surjective (frobenius R p)) (e : ℕ → R)
    (he0 : e 0 = 0) (he : ∀ n, e (n + 1) ^ p = e n)
    (hker : ∀ x : R, x ^ p = 0 ↔ x ∈ Ideal.span {e 1}) (n : ℕ) :
    RingHom.ker (iterateFrobenius R p n) = Ideal.span {e n} := by
  ext x
  rw [RingHom.mem_ker, iterateFrobenius_def]
  exact frobenius_pow_kernel_iff_mem_span R p hF e he0 he hker n x

end SerrePositivity

end FrobeniusRootKernelsPart

section PerfectionPrincipalKernelPart

namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- 各成分の割り算を両立する商の列へまとめる。
正の段で生成元の零化元がFrobeniusで消えることが、選択の誤差を除く。 -/
theorem perfection_dvd_of_coeff_dvd_of_annihilator (d x : Perfection R p)
    (hdiv : ∀ n, Perfection.coeff R p n d ∣ Perfection.coeff R p n x)
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p = 0) : d ∣ x := by
  choose a ha using hdiv
  have herr (n : ℕ) :
      Perfection.coeff R p n d * (a n - a (n + 1) ^ p) = 0 := by
    rw [mul_sub, ← ha n, ← Perfection.coeff_pow_p' d n, ← mul_pow,
      ← ha (n + 1), Perfection.coeff_pow_p', sub_self]
  have hcompat (n : ℕ) : (a (n + 2) ^ p) ^ p = a (n + 1) ^ p := by
    have h := hann n (a (n + 1) - a (n + 2) ^ p) (herr (n + 1))
    rw [sub_pow_char, sub_eq_zero] at h
    exact h.symm
  let b : Perfection R p := ⟨fun n ↦ a (n + 1) ^ p, hcompat⟩
  refine ⟨b, ?_⟩
  apply Perfection.ext
  intro n
  change Perfection.coeff R p n x =
    Perfection.coeff R p n d * a (n + 1) ^ p
  rw [← Perfection.coeff_pow_p' d n, ← mul_pow, ← ha (n + 1),
    Perfection.coeff_pow_p']

/-- 最初のFrobenius核と零化元の条件から、第0射影の核を主イデアルとして計算する。 -/
theorem perfection_coeff_zero_kernel_eq_span
    (hF : Function.Surjective (frobenius R p)) (d : Perfection R p)
    (hd0 : Perfection.coeff R p 0 d = 0)
    (hker : ∀ z : R, z ^ p = 0 ↔ z ∈ Ideal.span {Perfection.coeff R p 1 d})
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p = 0) :
    RingHom.ker (Perfection.coeff R p 0) = Ideal.span {d} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply perfection_dvd_of_coeff_dvd_of_annihilator R p d x _ hann
    intro n
    apply Ideal.mem_span_singleton.mp
    apply (frobenius_pow_kernel_iff_mem_span R p hF
      (fun k ↦ Perfection.coeff R p k d) hd0
      (fun k ↦ Perfection.coeff_pow_p' d k) hker n _).mp
    have h := compatibleRoots_pow p (fun k ↦ Perfection.coeff R p k x)
      (fun k ↦ Perfection.coeff_pow_p' x k) 0 n
    simpa only [Nat.zero_add, show Perfection.coeff R p 0 x = 0 from hx] using h
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hd0

end SerrePositivity

end PerfectionPrincipalKernelPart

section PerfectionKernelLiftPart

namespace SerrePositivity
variable {A B : Type*} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- 第0成分を指定したperfectionの持ち上げ。核のFrobeniusの全射性が誤差を除く。 -/
theorem exists_perfection_lift_of_kernel_roots (f : A →+* B) (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a)
    (y : Perfection B p) (b : A) (hb : f b = Perfection.coeff B p 0 y) :
    ∃ x : Perfection A p, Perfection.map p f x = y ∧ Perfection.coeff A p 0 x = b := by
  have hstep : ∀ n a, f a = Perfection.coeff B p n y →
      ∃ c : A, f c = Perfection.coeff B p (n + 1) y ∧ c ^ p = a := by
    intro n a ha
    obtain ⟨c, hc⟩ := hf (Perfection.coeff B p (n + 1) y)
    have herr : f (c ^ p - a) = 0 := by
      rw [map_sub, map_pow, hc, Perfection.coeff_pow_p', ha, sub_self]
    obtain ⟨t, ht, htp⟩ := hroots _ herr
    refine ⟨c - t, ?_, ?_⟩
    · rw [map_sub, hc, ht, sub_zero]
    · rw [sub_pow_char, htp]
      ring
  let L (n : ℕ) := {a : A // f a = Perfection.coeff B p n y}
  let step (n : ℕ) (a : L n) : L (n + 1) :=
    ⟨Classical.choose (hstep n a.val a.property), (Classical.choose_spec
      (hstep n a.val a.property)).1⟩
  let a : ∀ n, L n := fun n ↦ Nat.rec (⟨b, hb⟩ : L 0) step n
  have ha (n : ℕ) : (a (n + 1)).val ^ p = (a n).val := by
    change (Classical.choose (hstep n (a n).val (a n).property)) ^ p = (a n).val
    exact (Classical.choose_spec (hstep n (a n).val (a n).property)).2
  refine ⟨⟨fun n ↦ (a n).val, ha⟩, ?_, rfl⟩
  ext n
  exact (a n).property

/-- この条件の下で、perfection上の射も全射。 -/
theorem perfection_map_surjective_of_kernel_roots (f : A →+* B)
    (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a) :
    Function.Surjective (Perfection.map p f) := by
  intro y
  obtain ⟨b, hb⟩ := hf (Perfection.coeff B p 0 y)
  obtain ⟨x, hx, _⟩ := exists_perfection_lift_of_kernel_roots p f hf hroots y b hb
  exact ⟨x, hx⟩

/-- 第0射影の核はperfection上の全射で像へ移る。第0成分を零として持ち上げる。 -/
theorem perfection_map_coeff_zero_kernel (f : A →+* B) (hf : Function.Surjective f)
    (hroots : ∀ a : A, f a = 0 → ∃ b : A, f b = 0 ∧ b ^ p = a) :
    (RingHom.ker (Perfection.coeff A p 0)).map (Perfection.map p f) =
      RingHom.ker (Perfection.coeff B p 0) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change Perfection.coeff B p 0 (Perfection.map p f x) = 0
    rw [Perfection.coeff_map, show Perfection.coeff A p 0 x = 0 from hx, map_zero]
  · intro y hy
    obtain ⟨x, hx, hx0⟩ := exists_perfection_lift_of_kernel_roots p f hf hroots y 0
      (by rw [map_zero]; exact hy.symm)
    rw [← hx]
    exact Ideal.mem_map_of_mem _ hx0

end SerrePositivity

end PerfectionKernelLiftPart

section PerfectionIdealCorrectionPart

namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- p乗根を取れるイデアル内に列の誤差があれば、イデアル内の補正で互換列になる。 -/
theorem exists_perfection_of_errors_in_ideal (J : Ideal R)
    (hroots : ∀ u : J, ∃ v : J, (v : R) ^ p = u)
    (c : ℕ → R) (herr : ∀ n, c n - c (n + 1) ^ p ∈ J) :
    ∃ b : Perfection R p, ∀ n, Perfection.coeff R p n b - c n ∈ J := by
  let step (n : ℕ) (u : J) : J := Classical.choose
    (hroots ⟨c n - c (n + 1) ^ p + u, J.add_mem (herr n) u.property⟩)
  let u : ℕ → J := fun n ↦ Nat.rec 0 step n
  have hu (n : ℕ) : (u (n + 1)).val ^ p = c n - c (n + 1) ^ p + (u n).val := by
    exact Classical.choose_spec
      (hroots ⟨c n - c (n + 1) ^ p + (u n).val, J.add_mem (herr n) (u n).property⟩)
  have hb (n : ℕ) : (c (n + 1) + (u (n + 1)).val) ^ p = c n + (u n).val := by
    rw [add_pow_char, hu]
    ring
  refine ⟨⟨fun n ↦ c n + (u n).val, hb⟩, ?_⟩
  intro n
  change c n + (u n).val - c n ∈ J
  simpa only [add_sub_cancel_left] using (u n).property

/-- 座標の零化元のp乗が根を持つイデアルに入り、そのイデアルを生成元が零化すれば、
座標ごとの商を補正してperfection上の商を得る。 -/
theorem perfection_dvd_of_coeff_dvd_of_ideal_correction
    (d x : Perfection R p) (J : Ideal R)
    (hroots : ∀ u : J, ∃ v : J, (v : R) ^ p = u)
    (hkill : ∀ n z, z ∈ J → Perfection.coeff R p n d * z = 0)
    (hdiv : ∀ n, Perfection.coeff R p n d ∣ Perfection.coeff R p n x)
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p ∈ J) : d ∣ x := by
  choose a ha using hdiv
  have herr (n : ℕ) :
      Perfection.coeff R p n d * (a n - a (n + 1) ^ p) = 0 := by
    rw [mul_sub, ← ha n, ← Perfection.coeff_pow_p' d n, ← mul_pow,
      ← ha (n + 1), Perfection.coeff_pow_p', sub_self]
  let c : ℕ → R := fun n ↦ a (n + 1) ^ p
  have hc (n : ℕ) : c n - c (n + 1) ^ p ∈ J := by
    have h := hann n (a (n + 1) - a (n + 2) ^ p) (herr (n + 1))
    rw [sub_pow_char] at h
    exact h
  obtain ⟨b, hb⟩ := exists_perfection_of_errors_in_ideal R p J hroots c hc
  refine ⟨b, ?_⟩
  apply Perfection.ext
  intro n
  have hz := hkill n _ (hb n)
  rw [mul_sub, sub_eq_zero] at hz
  change Perfection.coeff R p n x = Perfection.coeff R p n d * Perfection.coeff R p n b
  rw [hz]
  change Perfection.coeff R p n x = Perfection.coeff R p n d * a (n + 1) ^ p
  rw [← Perfection.coeff_pow_p' d n, ← mul_pow, ← ha (n + 1), Perfection.coeff_pow_p']

end SerrePositivity

end PerfectionIdealCorrectionPart

section PerfectAnnihilatorPart

namespace SerrePositivity
variable (k : Type*) [CommRing k]

/-- 一元の零化イデアル。 -/
def principalAnnihilator (a : k) : Ideal k := (Submodule.span k {a}).annihilator

/-- 零化イデアルの所属条件。 -/
theorem mem_principalAnnihilator (a z : k) : z ∈ principalAnnihilator k a ↔ a * z = 0 := by
  rw [principalAnnihilator, Submodule.mem_annihilator_span_singleton]
  change z * a = 0 ↔ a * z = 0
  rw [mul_comm]

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

omit [CharP k p] in
/-- 完全環の零化イデアル内でp乗根を選べる。 -/
theorem principalAnnihilator_has_p_roots (a : k) (u : principalAnnihilator k a) :
    ∃ v : principalAnnihilator k a, (v : k) ^ p = u := by
  obtain ⟨v, hv⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (u : k)
  have hu := (mem_principalAnnihilator k a u).mp u.property
  have hvann : a * v = 0 := by
    apply (PerfectRing.bijective_frobenius (R := k) (p := p)).1
    change (a * v) ^ p = (0 : k) ^ p
    change v ^ p = (u : k) at hv
    rw [mul_pow, hv]
    have h := pow_mul_eq_zero_of_le (a := a) (b := (u : k))
      (m := 1) (n := p) (Fact.out : p.Prime).one_lt.le (by simpa using hu)
    simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using h
  exact ⟨⟨v, (mem_principalAnnihilator k a v).mpr hvann⟩, hv⟩

/-- aのp冪根もann(a)を零化する。 -/
theorem principalAnnihilator_killed_by_p_root (a r : k) (n : ℕ) (hr : r ^ p ^ n = a)
    (z : k) (hz : z ∈ principalAnnihilator k a) : r * z = 0 := by
  have ha := (mem_principalAnnihilator k a z).mp hz
  apply (bijective_iterateFrobenius k p n).1
  change (r * z) ^ p ^ n = (0 : k) ^ p ^ n
  rw [mul_pow, hr]
  have h := pow_mul_eq_zero_of_le (a := z) (b := a) (m := 1) (n := p ^ n)
    (Nat.one_le_pow n p (Fact.out : p.Prime).pos)
    (by simpa only [pow_one, mul_comm] using ha)
  simpa only [mul_comm, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] using h

/-- 主イデアル商への零化イデアルの像。 -/
def quotientAnnihilatorImage (a : k) : Ideal (k ⧸ Ideal.span {a}) :=
  (principalAnnihilator k a).map (Ideal.Quotient.mk (Ideal.span {a}))

omit [CharP k p] in
/-- 商への像もイデアル内でp乗根を持つ。 -/
theorem quotientAnnihilatorImage_has_p_roots (a : k) (u : quotientAnnihilatorImage k a) :
    ∃ v : quotientAnnihilatorImage k a, (v : k ⧸ Ideal.span {a}) ^ p = u := by
  obtain ⟨t, ht, htu⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp u.property
  obtain ⟨v, hv⟩ := principalAnnihilator_has_p_roots k p a ⟨t, ht⟩
  refine ⟨⟨Ideal.Quotient.mk (Ideal.span {a}) v, Ideal.mem_map_of_mem _ v.property⟩, ?_⟩
  rw [← map_pow, hv, htu]

/-- 商でaのp冪根は零化イデアルの像を零化する。 -/
theorem quotientAnnihilatorImage_killed_by_p_root (a r : k) (n : ℕ)
    (hr : r ^ p ^ n = a) (z : k ⧸ Ideal.span {a})
    (hz : z ∈ quotientAnnihilatorImage k a) : Ideal.Quotient.mk (Ideal.span {a}) r * z = 0 := by
  obtain ⟨t, ht, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz
  rw [← map_mul, principalAnnihilator_killed_by_p_root k p a r n hr t ht, map_zero]

omit [PerfectRing k p] in
/-- 正のp冪根の零化元のp乗は、商の零化イデアル像へ入る。
生成元の正則性を仮定せず、割り算の誤差をイデアルへ隔離する。 -/
theorem quotient_p_root_annihilator_pow_mem (a r : k) (n : ℕ)
    (hr : r ^ p ^ (n + 1) = a) (z : k ⧸ Ideal.span {a})
    (hz : Ideal.Quotient.mk (Ideal.span {a}) r * z = 0) :
    z ^ p ∈ quotientAnnihilatorImage k a := by
  let q := Ideal.Quotient.mk (Ideal.span {a})
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hm : r * t ∈ Ideal.span {a} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  let N := p ^ (n + 1)
  have hN : 2 ≤ N := (Fact.out : p.Prime).two_le.trans
    (Nat.le_self_pow (by omega : n + 1 ≠ 0) p)
  have hn : N - 1 + 1 = N := by omega
  let u := t - r ^ (N - 1) * c
  have hru : r * u = 0 := by
    dsimp only [u]
    rw [mul_sub, hc, ← hr]
    change r ^ N * c - r * (r ^ (N - 1) * c) = 0
    rw [← mul_assoc, ← pow_succ', hn, sub_self]
  have hau : a * u = 0 := by
    rw [← hr]
    change r ^ N * u = 0
    exact pow_mul_eq_zero_of_le (by omega : 1 ≤ N) (by simpa only [pow_one] using hru)
  have hup : u ^ p ∈ principalAnnihilator k a := by
    apply (mem_principalAnnihilator k a _).mpr
    have h := pow_mul_eq_zero_of_le (a := u) (b := a) (m := 1) (n := p)
      (Fact.out : p.Prime).one_lt.le (by simpa only [pow_one, mul_comm] using hau)
    simpa only [mul_comm] using h
  have hvanish : q ((r ^ (N - 1) * c) ^ p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [mul_pow, ← pow_mul]
    apply (Ideal.span {a}).mul_mem_right
    apply (Ideal.span {a}).pow_mem_of_pow_mem (m := N) _
      (by have hp := (Fact.out : p.Prime).two_le; nlinarith : N ≤ (N - 1) * p)
    rw [show r ^ N = a from hr]
    exact Ideal.mem_span_singleton_self a
  have he : q t ^ p = q (u ^ p) := by
    have ht : t = r ^ (N - 1) * c + u := by dsimp only [u]; ring
    rw [ht, ← map_pow, add_pow_char, map_add, hvanish, zero_add]
  rw [he]
  exact Ideal.mem_map_of_mem q hup

end SerrePositivity

end PerfectAnnihilatorPart

section PerfectionPrincipalQuotientKernelPart

namespace SerrePositivity
variable (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

section Quotient
variable (a : k) [CharP (k ⧸ Ideal.span {a}) p]

/-- 完全環から主イデアル商のperfectionへの標準環準同型。 -/
def principalQuotientPerfectionLift : k →+* Perfection (k ⧸ Ideal.span {a}) p :=
  Perfection.lift p k (k ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}))

/-- 標準写像の各座標。 -/
theorem principalQuotientPerfectionLift_coeff (b : k) (n : ℕ) :
    Perfection.coeff (k ⧸ Ideal.span {a}) p n (principalQuotientPerfectionLift k p a b) =
      Ideal.Quotient.mk (Ideal.span {a}) (((frobeniusEquiv k p).symm : k → k)^[n] b) :=
  rfl

/-- 第0射影核の元は全座標で標準生成元により割り切れる。 -/
theorem principalQuotientPerfectionLift_coeff_dvd
    (x : Perfection (k ⧸ Ideal.span {a}) p)
    (hx : Perfection.coeff (k ⧸ Ideal.span {a}) p 0 x = 0) (n : ℕ) :
    Perfection.coeff (k ⧸ Ideal.span {a}) p n (principalQuotientPerfectionLift k p a a) ∣
      Perfection.coeff (k ⧸ Ideal.span {a}) p n x := by
  let q := Ideal.Quotient.mk (Ideal.span {a})
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff (k ⧸ Ideal.span {a}) p n x)
  have hpow : q (t ^ p ^ n) = 0 := by
    rw [map_pow, ht]
    have he := Perfection.coeffMonoidHom_pow_p_pow_self x n
    change (Perfection.coeff (k ⧸ Ideal.span {a}) p n x) ^ p ^ n =
      Perfection.coeff (k ⧸ Ideal.span {a}) p 0 x at he
    rw [he, hx]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hpow)
  have he : t = ((frobeniusEquiv k p).symm : k → k)^[n] a *
      ((frobeniusEquiv k p).symm : k → k)^[n] c := by
    apply (bijective_iterateFrobenius k p n).1
    change t ^ p ^ n =
      (((frobeniusEquiv k p).symm : k → k)^[n] a *
        ((frobeniusEquiv k p).symm : k → k)^[n] c) ^ p ^ n
    rw [mul_pow, iterate_frobeniusEquiv_symm_pow_p_pow, iterate_frobeniusEquiv_symm_pow_p_pow]
    exact hc
  rw [principalQuotientPerfectionLift_coeff, ← ht, he, map_mul]
  exact dvd_mul_right _ _

/-- 任意の零因子も含む、主イデアル商のperfectionの第0射影核の生成公式。 -/
theorem perfection_principal_quotient_coeff_zero_kernel_eq_span :
    RingHom.ker (Perfection.coeff (k ⧸ Ideal.span {a}) p 0) =
      Ideal.span {principalQuotientPerfectionLift k p a a} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply perfection_dvd_of_coeff_dvd_of_ideal_correction (k ⧸ Ideal.span {a}) p
      (principalQuotientPerfectionLift k p a a) x (quotientAnnihilatorImage k a)
    · exact quotientAnnihilatorImage_has_p_roots k p a
    · intro n z hz
      rw [principalQuotientPerfectionLift_coeff]
      exact quotientAnnihilatorImage_killed_by_p_root k p a _ n
        (iterate_frobeniusEquiv_symm_pow_p_pow k p a n) z hz
    · exact principalQuotientPerfectionLift_coeff_dvd k p a x hx
    · intro n z hz
      rw [principalQuotientPerfectionLift_coeff] at hz
      exact quotient_p_root_annihilator_pow_mem k p a _ n
        (iterate_frobeniusEquiv_symm_pow_p_pow k p a (n + 1)) z hz
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change Perfection.coeff (k ⧸ Ideal.span {a}) p 0 (principalQuotientPerfectionLift k p a a) = 0
    rw [principalQuotientPerfectionLift_coeff]
    change Ideal.Quotient.mk (Ideal.span {a}) a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)

/-- BS要求の標準Perfection.liftをそのまま使う公開署名。 -/
theorem perfection_lift_principal_quotient_kernel :
    RingHom.ker (Perfection.coeff (k ⧸ Ideal.span {a}) p 0) =
      Ideal.span {((Perfection.lift p k (k ⧸ Ideal.span {a}))
        (Ideal.Quotient.mk (Ideal.span {a}))) a} :=
  perfection_principal_quotient_coeff_zero_kernel_eq_span k p a

end Quotient

end SerrePositivity

end PerfectionPrincipalQuotientKernelPart

section PrincipalQuotientAnnihilatorPart

namespace SerrePositivity
variable (R : Type*) [CommRing R]

/-- 正則元の冪による商で、その元の零化元は指定した冪で消える。 -/
theorem pow_eq_zero_of_mul_eq_zero_mod_regular_pow (r : R)
    (hreg : Function.Injective (fun z : R ↦ r * z)) (N k : ℕ) (hN : 0 < N)
    (hbound : N ≤ (N - 1) * k) (z : R ⧸ Ideal.span {r ^ N})
    (hz : Ideal.Quotient.mk (Ideal.span {r ^ N}) r * z = 0) : z ^ k = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have ha : r * a ∈ Ideal.span {r ^ N} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hab : a = r ^ (N - 1) * b := by
    apply hreg
    change r * a = r * (r ^ (N - 1) * b)
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN]
    exact hb
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  rw [hab, mul_pow, ← pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow r hbound) _

end SerrePositivity

end PrincipalQuotientAnnihilatorPart
