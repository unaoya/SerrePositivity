module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Algebra.CharP.Algebra
public import SerrePositivity.CommutativeAlgebra.FrobeniusKernelLift

/-! # 完全環からの写像の冪零核を越える持ち上げ

標数pでは、核を消すFrobenius冪を全射に沿って降ろし、
完全な源の逆Frobeniusを合成して実際の環写像を構成する。
局所性・Noether性・有限生成性は要求しない。
-/

public section
namespace SerrePositivity
open IsAdicComplete

/-- 核を一つのFrobenius冪が消す全射に沿って、完全環からの写像は一意に持ち上がる。 -/
theorem exists_unique_ringHom_lift_of_frobenius_kernel
    (p : ℕ) [Fact p.Prime] {A B k : Type*}
    [CommRing A] [CommRing B] [CommRing k]
    [CharP A p] [CharP B p] [CharP k p] [PerfectRing k p]
    (f : A →+* B) (hf : Function.Surjective f) (n : ℕ)
    (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (g : k →+* B) :
    ∃! l : k →+* A, f.comp l = g := by
  let T := liftFrobeniusOfSurjective p f hf n hkill
  have hfT (b : B) : f (T b) = iterateFrobenius B p n b := by
    exact map_liftFrobeniusOfSurjective p f hf n hkill b
  let e := iterateFrobeniusEquiv k p n
  let l : k →+* A := T.comp (g.comp e.symm.toRingHom)
  have hl : f.comp l = g := by
    ext x
    change f (T (g (e.symm x))) = g x
    rw [hfT, ← g.map_iterateFrobenius p (e.symm x) n]
    exact congrArg g (e.apply_symm_apply x)
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  ext x
  let y := e.symm x
  have hy : y ^ p ^ n = x := e.apply_symm_apply x
  have hz : (l' y - l y) ^ p ^ n = 0 := by
    apply hkill
    simp only [map_sub]
    change (f.comp l') y - (f.comp l) y = 0
    rw [hl', hl, sub_self]
  rw [sub_pow_expChar_pow, ← l'.map_pow, ← l.map_pow, hy] at hz
  exact sub_eq_zero.mp hz

/-- 冪零核を持つ全射に沿う完全環からの写像の一意な持ち上げ。 -/
theorem exists_unique_ringHom_lift_of_nilpotent_kernel
    (p : ℕ) [hp : Fact p.Prime] {A B k : Type*}
    [CommRing A] [CommRing B] [CommRing k]
    [CharP A p] [CharP B p] [CharP k p] [PerfectRing k p]
    (f : A →+* B) (hf : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f)) (g : k →+* B) :
    ∃! l : k →+* A, f.comp l = g := by
  obtain ⟨n, hn⟩ := exists_pow_exp_eq_zero_of_nilpotent_ideal p (RingHom.ker f) hker
  exact exists_unique_ringHom_lift_of_frobenius_kernel p f hf n (fun x hx ↦ hn x hx) g

/-- 標数pのI進完備環では、完全環からI商への写像は一意に持ち上がる。
各正の冪商での一意な持ち上げを両立させて逆極限を取る。 -/
theorem exists_unique_ringHom_lift_of_adicComplete
    (p : ℕ) [hp : Fact p.Prime] {R k : Type*} [CommRing R] [CommRing k]
    [CharP R p] [CharP k p] [PerfectRing k p]
    (I : Ideal R) [IsAdicComplete I R] [CharP (R ⧸ I) p] (g : k →+* R ⧸ I) :
    ∃! l : k →+* R, (Ideal.Quotient.mk I).comp l = g := by
  classical
  let q (n : ℕ) : R ⧸ I ^ (n + 1) →+* R ⧸ I :=
    Ideal.Quotient.factor (I.pow_le_self (Nat.succ_ne_zero n))
  have hq (n : ℕ) : ∃! l : k →+* R ⧸ I ^ (n + 1), (q n).comp l = g := by
    let : CharP (R ⧸ I ^ (n + 1)) p := CharP.quotient' p _ (fun a ha ↦ by
      have h : (a : R ⧸ I) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
        exact I.pow_le_self (Nat.succ_ne_zero n) ha
      exact (CharP.cast_eq_zero_iff R p a).mpr
        ((CharP.cast_eq_zero_iff (R ⧸ I) p a).mp h))
    have ha : n + 1 < p ^ (n + 1) := Nat.lt_pow_self hp.out.one_lt
    apply exists_unique_ringHom_lift_of_frobenius_kernel p (q n)
      (Ideal.Quotient.factor_surjective _) (n + 1)
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ I := by
      simpa only [q, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hx
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right ha.le (Ideal.pow_mem_pow hr _)
  choose L hL huniq using hq
  have hc (n : ℕ) : (Ideal.Quotient.factorPowSucc I (n + 1)).comp (L (n + 1)) = L n := by
    apply huniq n
    rw [← RingHom.comp_assoc]
    have he : (q n).comp (Ideal.Quotient.factorPowSucc I (n + 1)) = q (n + 1) := by
      ext r
      simp [q]
    rw [he, hL]
  have hc' : ∀ {n}, (Ideal.Quotient.factorPow I
      (Order.succ_strictMono.monotone (Nat.le_succ n))).comp (L (n + 1)) = L n :=
    fun {n} ↦ hc n
  let l := Order.succ_strictMono.liftRingHom I L hc'
  have hl : (Ideal.Quotient.mk I).comp l = g := by
    ext x
    have he : Ideal.Quotient.mk (I ^ (0 + 1)) (l x) = L 0 x :=
      Order.succ_strictMono.mk_liftRingHom I L hc' (n := 0) x
    have h := RingHom.congr_fun (hL 0) x
    change q 0 (L 0 x) = g x at h
    rw [← he] at h
    simpa [q] using h
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  ext x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have he : (Ideal.Quotient.mk (I ^ (n + 1))).comp l' = L n := by
      apply huniq n
      rw [← RingHom.comp_assoc]
      have h : (q n).comp (Ideal.Quotient.mk (I ^ (n + 1))) = Ideal.Quotient.mk I := by
        ext; simp [q]
      rw [h, hl']
    have hx := RingHom.congr_fun he x
    have hy : Ideal.Quotient.mk (I ^ (n + 1)) (l x) = L n x :=
      Order.succ_strictMono.mk_liftRingHom I L hc' (n := n) x
    simpa only [smul_eq_mul, Ideal.mul_top] using
      (SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp (hx.trans hy.symm)) :
        l' x ≡ l x [SMOD I ^ (n + 1)])

/-- 全射の核について完備なら、完全環からの写像は全射を越えて一意に持ち上がる。 -/
theorem exists_unique_ringHom_lift_of_complete_kernel
    (p : ℕ) [Fact p.Prime] {A B k : Type*}
    [CommRing A] [CommRing B] [CommRing k]
    [CharP A p] [CharP B p] [CharP k p] [PerfectRing k p]
    (f : A →+* B) (hf : Function.Surjective f)
    [IsAdicComplete (RingHom.ker f) A] (g : k →+* B) :
    ∃! l : k →+* A, f.comp l = g := by
  let e := RingHom.quotientKerEquivOfSurjective hf
  let : CharP (A ⧸ RingHom.ker f) p := e.toRingHom.charP e.injective p
  obtain ⟨l, hl, huniq⟩ := exists_unique_ringHom_lift_of_adicComplete p
    (RingHom.ker f) (e.symm.toRingHom.comp g)
  have he : e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := by
    ext; rfl
  have hl' : f.comp l = g := by
    rw [← he, RingHom.comp_assoc, hl, ← RingHom.comp_assoc]
    simp
  refine ⟨l, hl', ?_⟩
  intro l' hl''
  apply huniq
  ext x
  apply e.injective
  change e (Ideal.Quotient.mk (RingHom.ker f) (l' x)) = e (e.symm (g x))
  rw [e.apply_symm_apply]
  exact RingHom.congr_fun hl'' x

end SerrePositivity
