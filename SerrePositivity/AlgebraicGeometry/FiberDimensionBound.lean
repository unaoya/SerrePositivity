module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import SerrePositivity.AlgebraicGeometry.FiberNoetherNormalization
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
概要：ファイバーの指定点の周りで次元の上限を多項式による正規化に渡す。
方針：不要な極小素イデアルを一つの主開で除き、有限単射で素イデアルの鎖を比較する。
規約：点での次元の上限は、その点を含む各既約成分の次元の上限で表す。
使われ方：相対 Noether 正規化で多項式環の変数の数を制御する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped BigOperators TensorProduct

/--
概要：有限単射で結ばれた環の Krull 次元は等しい。
方針：非比較性で素イデアルの鎖を引き戻し、lying over と going up で持ち上げる。
規約：零環も含めて次元を `WithBot ℕ∞` で測る。
使われ方：Noether 正規化で得られる多項式の変数の数を数える。
-/
theorem ringKrullDim_eq_of_injective_finite
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Finite) (hinj : Function.Injective f) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  let : Module.Finite A B := hf
  let g := PrimeSpectrum.comap (algebraMap A B)
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono g
    intro P Q hPQ
    have hle : g P ≤ g Q := Ideal.comap_mono hPQ.le
    refine lt_of_le_of_ne hle fun heq => hPQ.ne (PrimeSpectrum.ext ?_)
    exact Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hPQ.le
      (congrArg PrimeSpectrum.asIdeal heq)
  · change Order.krullDim (PrimeSpectrum A) ≤ Order.krullDim (PrimeSpectrum B)
    rw [Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨P, hP⟩ := hf.to_isIntegral.comap_surjective hinj p.head
    let : P.asIdeal.LiesOver p.head.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hP.symm⟩
    obtain ⟨q, hq, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp p P.asIdeal
    rw [← hq]
    exact le_iSup (fun q : LTSeries (PrimeSpectrum B) => (q.length : WithBot ℕ∞)) q

/--
概要：Noether 環の点を含む既約成分の次元がすべて上限以下なら、その点を含む主開の
Krull 次元もその上限以下にできる。
方針：点を含まない極小素イデアルから点を避ける元を選び、その積を反転する。
規約：既約成分の次元は極小素イデアルによる商環の Krull 次元。
使われ方：ファイバー上の正規化で、指定点に不要な成分を取り除く。
-/
theorem exists_away_ringKrullDim_le_of_minimalPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] (q : Ideal A) [q.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes A, m ≤ q → ringKrullDim (A ⧸ m) ≤ d) :
    ∃ a : A, a ∉ q ∧ ringKrullDim (Localization.Away a) ≤ d := by
  classical
  let bad := {m ∈ minimalPrimes A | ¬ m ≤ q}
  have hbad : bad.Finite := (minimalPrimes.finite_of_isNoetherianRing A).subset fun _ h => h.1
  have hchoose (m : bad) : ∃ a : A, a ∈ m.1 ∧ a ∉ q := by
    by_contra! h
    exact m.2.2 (fun x hx => h x hx)
  choose a ha hq using hchoose
  let : Fintype bad := hbad.fintype
  let s := ∏ m, a m
  have hs : s ∉ q := by
    exact fun h => (Ideal.IsPrime.prod_mem_iff.mp h).elim fun m hm => hq m hm.2
  refine ⟨s, hs, ?_⟩
  let e := IsLocalization.primeSpectrumOrderIso (.powers s) (Localization.Away s)
  rw [ringKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  let P := (e p.head).1
  obtain ⟨m, hm, hmP⟩ := Ideal.exists_minimalPrimes_le (J := P.asIdeal) bot_le
  have hms : s ∉ m := by
    intro h
    exact Set.disjoint_left.mp (e p.head).2 (Submonoid.mem_powers s) (hmP h)
  have hmq : m ≤ q := by
    by_contra h
    let j : bad := ⟨m, hm, h⟩
    apply hms
    dsimp only [s]
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ j)]
    exact m.mul_mem_right _ (ha j)
  let z (i : Fin (p.length + 1)) : PrimeSpectrum.zeroLocus (m : Set A) :=
    ⟨(e (p i)).1, hmP.trans (e.monotone (p.head_le i))⟩
  let p' := LTSeries.mk p.length z
    (fun i j h => show (e (p i)).1 < (e (p j)).1 from e.strictMono (p.strictMono h))
  have hp' : (p.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ m) := by
    rw [ringKrullDim_quotient, Order.krullDim]
    exact le_iSup (fun l : LTSeries (PrimeSpectrum.zeroLocus (m : Set A)) =>
      (l.length : WithBot ℕ∞)) p'
  exact hp'.trans (hd m hm hmq)

/--
概要：指定点を含む既約成分の次元の上限は、元の代数の主開にファイバーを制限して
ファイバー全体の次元の上限にできる。
方針：ファイバー上で選んだ主開の分母を払い、単元倍で局所化が変わらないことを使う。
規約：ファイバー上の指定点は、そのファイバー代数の素イデアルで表す。
使われ方：相対 Noether 正規化に入る前に、指定点の周りでファイバーの次元を抑える。
-/
theorem exists_fiber_away_ringKrullDim_le
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.ResidueField ⊗[R] B), m ≤ z →
      ringKrullDim ((p.ResidueField ⊗[R] B) ⧸ m) ≤ d) :
    ∃ b : B, ((1 : p.ResidueField) ⊗ₜ[R] b) ∉ z ∧
      ringKrullDim (p.ResidueField ⊗[R] Localization.Away b) ≤ d := by
  let K := p.ResidueField
  let A := K ⊗[R] B
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨a, ha, hdim⟩ := exists_away_ringKrullDim_le_of_minimalPrimes z d hd
  obtain ⟨s, b, hs, hb⟩ := exists_fiber_denominator p a
  let c := (1 : K) ⊗ₜ[R] b
  have he : a * algebraMap K A (algebraMap R K s) = c := by
    rw [mul_comm, ← Algebra.smul_def]
    exact hb
  have hu : IsUnit (algebraMap K A (algebraMap R K s)) :=
    (isUnit_iff_ne_zero.mpr fun h => hs (Ideal.algebraMap_residueField_eq_zero.mp h)).map
      (algebraMap K A)
  obtain ⟨u, hu⟩ := hu
  have hac : Associated a c := ⟨u, hu ▸ he⟩
  refine ⟨b, ?_, ?_⟩
  · intro hc
    have hmem : a * ↑u ∈ z := by simpa only [hu, he] using hc
    exact ha ((Ideal.mul_unit_mem_iff_mem z u.isUnit).mp hmem)
  · let : IsLocalization.Away c (Localization.Away a) :=
      IsLocalization.Away.of_associated (S := Localization.Away a) hac
    let e := IsLocalization.Away.tensorProductEquivTMulRight R K b (Localization.Away b)
    let l := IsLocalization.algEquiv (.powers c) (Localization.Away c) (Localization.Away a)
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ringKrullDim_eq_of_ringEquiv l.toRingEquiv]
    exact hdim

/--
概要：指定点を含む主開に制限したファイバーに、その Krull 次元と同じ数の変数で
有限単射となる Noether 正規化が存在する。
方針：ファイバーの不要な成分を除き、有限単射と多項式環の次元を比較する。
規約：評価する変数の値は、元の代数を主開に制限した環の元で選ぶ。
使われ方：相対 Noether 正規化のアフィン空間の相対次元に上限を与える。
-/
theorem exists_fiber_noether_normalization_of_dim_le
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.ResidueField ⊗[R] B), m ≤ z →
      ringKrullDim ((p.ResidueField ⊗[R] B) ⧸ m) ≤ d) :
    ∃ a : B, ((1 : p.ResidueField) ⊗ₜ[R] a) ∉ z ∧
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away a,
        ringKrullDim (p.ResidueField ⊗[R] Localization.Away a) = n ∧ (n : WithBot ℕ∞) ≤ d ∧
        let f := MvPolynomial.aeval (R := p.ResidueField)
          (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)
        Function.Injective f ∧ f.Finite := by
  obtain ⟨a, ha, hdim⟩ := exists_fiber_away_ringKrullDim_le p z d hd
  let K := p.ResidueField
  let L := Localization.Away a
  let c := (1 : K) ⊗ₜ[R] a
  let e := IsLocalization.Away.tensorProductEquivTMulRight R K a L
  let eSpec := IsLocalization.primeSpectrumOrderIso (.powers c) (Localization.Away c)
  let z' : PrimeSpectrum (Localization.Away c) :=
    eSpec.symm ⟨⟨z, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime c).mpr ha⟩
  let : Nontrivial (Localization.Away c) := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨z'⟩
  let : Nontrivial (K ⊗[R] L) := e.toRingEquiv.surjective.nontrivial
  let : Algebra.FiniteType R L := Algebra.FiniteType.trans ‹Algebra.FiniteType R B›
    (inferInstance : Algebra.FiniteType B L)
  obtain ⟨n, b, hinj, hfin⟩ := exists_fiber_noether_normalization_generators (B := L) p
  have hdim' : ringKrullDim (K ⊗[R] L) = n := by
    rw [ringKrullDim_eq_of_injective_finite _ hfin hinj,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  exact ⟨a, ha, n, b, hdim', hdim' ▸ hdim, hinj, hfin⟩

end SerrePositivity.AlgebraicGeometry
