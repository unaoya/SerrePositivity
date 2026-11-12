module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：射影 Čech コホモロジーの有限性に使う指数の評価と降下帰納。
方針：単項式の残る指数を有限区間に入れ、有限自由表示からの長完全列を使う。
規約：次数の上界は消滅が始まる最初の次数とする。
使われ方：多項式環の捻りの計算から有限生成次数付き加群の有限性へ進む。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- 全指数が非負で総次数が固定された単項式は有限個。 -/
theorem finite_projectiveCechNonnegativeExponents (d : ℤ) :
    Finite {e : ι → ℤ // (∀ i, 0 ≤ e i) ∧ (∑ i, e i) = d} := by
  classical
  let : Finite (Set.Icc (0 : ℤ) d) := (Set.finite_Icc _ _).to_subtype
  let f : {e : ι → ℤ // (∀ i, 0 ≤ e i) ∧ (∑ i, e i) = d} →
      (ι → Set.Icc (0 : ℤ) d) := fun e i ↦ ⟨e.val i, e.property.1 i, by
        calc
          e.val i ≤ ∑ j, e.val j :=
            Finset.single_le_sum (fun j _ ↦ e.property.1 j) (Finset.mem_univ i)
          _ = d := e.property.2⟩
  refine Finite.of_injective f fun e e' he ↦ Subtype.ext (funext fun i ↦ ?_)
  exact congrArg (fun a : ι → Set.Icc (0 : ℤ) d ↦ (a i).val) he

/-- 全指数が負で総次数が固定された Laurent 単項式は有限個。 -/
theorem finite_projectiveCechNegativeExponents (d : ℤ) :
    Finite {e : ι → ℤ // (∀ i, e i < 0) ∧ (∑ i, e i) = d} := by
  let := finite_projectiveCechNonnegativeExponents (ι := ι) (-d)
  let f : {e : ι → ℤ // (∀ i, e i < 0) ∧ (∑ i, e i) = d} →
      {e : ι → ℤ // (∀ i, 0 ≤ e i) ∧ (∑ i, e i) = -d} := fun e ↦
        ⟨fun i ↦ -e.val i, fun i ↦ neg_nonneg.mpr (e.property.1 i).le, by
          rw [Finset.sum_neg_distrib, e.property.2]⟩
  refine Finite.of_injective f fun e e' he ↦ Subtype.ext (funext fun i ↦ ?_)
  exact neg_injective (congrArg (fun a ↦ a.val i) he)

omit [Fintype ι] in
/--
概要：標準開で許される Laurent 単項式の分母を、チャートの積の一つの冪にそろえる。
方針：負の指数の絶対値の和で、各負の指数を一様に打ち消す。
規約：T の外の指数は非負とする。
使われ方：多項式環の次数付き局所化を Laurent 単項式の基底で表示する。
-/
theorem exists_projectiveCech_commonMonomialDenominator [Finite ι] [DecidableEq ι]
    (T : Finset ι) (e : ι → ℤ) (he : ∀ i ∉ T, 0 ≤ e i) :
    ∃ n : ℕ, ∀ i, 0 ≤ e i + (if i ∈ T then (n : ℤ) else 0) := by
  let : Fintype ι := Fintype.ofFinite ι
  let b : ℤ := ∑ i, max 0 (-e i)
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ ↦ le_max_left _ _
  refine ⟨b.toNat, fun i ↦ ?_⟩
  by_cases hi : i ∈ T
  · rw [ite_eq_left hi, Int.toNat_of_nonneg hb]
    have h : -e i ≤ b := (le_max_right 0 _).trans <|
      Finset.single_le_sum (fun j _ ↦ le_max_left 0 (-e j)) (Finset.mem_univ i)
    omega
  · simpa [hi] using he i hi

section DimensionShift

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {Obj : Type*} (H : Obj → ℕ → ModuleCat R) (bound : ℕ)

/--
概要：コホモロジーの有界性と有限自由表示から、各次数の有限性を出す。
方針：長完全列の三項を取り、右の写像の像と有限自由加群からの像で中項を評価する。
規約：自由表示の核は再び同じ種類の対象。自由項の有限性は別に計算して渡す。
使われ方：多項式環の捻りから一般の有限生成次数付き加群への降下帰納。
-/
theorem projectiveCechFinite_of_bounded_of_exact
    (hbound : ∀ M q, bound ≤ q → Module.Finite R (H M q))
    (hstep : ∀ M q, ∃ (F K : Obj) (f : H F q →ₗ[R] H M q)
      (g : H M q →ₗ[R] H K (q + 1)), Module.Finite R (H F q) ∧ Function.Exact f g) :
    ∀ M q, Module.Finite R (H M q) := by
  have hfinite (n : ℕ) : ∀ M q, bound ≤ q + n → Module.Finite R (H M q) := by
    induction n with
    | zero => simpa using hbound
    | succ n ih =>
      intro M q hq
      obtain ⟨F, K, f, g, hF, hexact⟩ := hstep M q
      let : Module.Finite R (H F q) := hF
      let : Module.Finite R (H K (q + 1)) := ih K (q + 1) (by omega)
      let : Module.Finite R (LinearMap.range g) := inferInstance
      refine Module.Finite.of_exact (f := f) (g := g.rangeRestrict) ?_ g.surjective_rangeRestrict
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
      exact LinearMap.exact_iff.mp hexact
  exact fun M q ↦ hfinite bound M q (by omega)

end DimensionShift

end SerrePositivity.AlgebraicGeometry
