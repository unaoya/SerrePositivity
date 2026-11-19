module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PowerCharts
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
概要：KST §5 の冪中心の blowup は元の中心の元の冪に対応するチャートで被覆される。
方針：I^n の積生成元の n 乗を純冪生成元の積に書き、素イデアルの判定を使う。
規約：n は正、有限生成性と Noether 性は要求しない。
使われ方：Bl_{I^n} と Bl_I のチャート同型を大域化する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial _root_.AlgebraicGeometry
open scoped Pointwise

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：I の n 個の元の積を I^n の元として束ねる。
方針：イデアルの積への所属と有限積の公式を使う。
規約：KST §5、n = 0 なら単位元を I^0 に入れる。
使われ方：イデアルの冪の積生成元を扱う。
-/
def productCenterElement (n : ℕ) (f : Fin n → I) : ↥(I ^ n) :=
  ⟨∏ i, (f i).1, by
    simpa using (Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ : Fin n => I)
      (x := fun i => (f i).1) (fun i _ => (f i).2))⟩

/--
概要：積生成元の次数一 Rees 元の n 乗は、純冪生成元の次数一 Rees 元の積。
方針：両辺を多項式環で単項式の積として計算する。
規約：KST §5、中心は I^n。
使われ方：冪チャートの被覆性を素イデアルの判定に帰着する。
-/
lemma reesDegreeOne_product_pow (n : ℕ) (f : Fin n → I) :
    reesDegreeOne (I ^ n) (productCenterElement I n f) ^ n =
      ∏ i, reesDegreeOne (I ^ n) (powerCenterElement I (f i) n) := by
  apply Subtype.ext
  simp [reesDegreeOne, reesMonomial, productCenterElement, powerCenterElement,
    ← C_mul_X_pow_eq_monomial, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow]

/--
概要：純冪チャートの全生成元を含む素イデアルは、冪中心の次数一元を全て含む。
方針：まず積生成元について n 乗を計算し、R 線形な逆像部分加群で和へ拡張する。
規約：KST §5、n > 0 と素性だけを使う。
使われ方：純冪チャートが Proj 全体を被覆することの環論的入力。
-/
theorem prime_contains_degreeOne_of_contains_powers (n : ℕ) (hn : 0 < n)
    (P : Ideal (reesAlgebra (I ^ n))) [P.IsPrime]
    (hP : ∀ a : I, reesDegreeOne (I ^ n) (powerCenterElement I a n) ∈ P) :
    ∀ b : ↥(I ^ n), reesDegreeOne (I ^ n) b ∈ P := by
  classical
  have hprod (f : Fin n → I) :
      reesDegreeOne (I ^ n) (productCenterElement I n f) ∈ P := by
    apply (Ideal.IsPrime.pow_mem_iff_mem inferInstance n hn).mp
    rw [reesDegreeOne_product_pow]
    exact P.prod_mem (i := ⟨0, hn⟩) (Finset.mem_univ _) (hP (f ⟨0, hn⟩))
  let T : Submodule R R :=
    ((P.restrictScalars R).map (reesAlgebra (I ^ n)).val.toLinearMap).comap (monomial 1)
  have hspan : I ^ n ≤ T := by
    rw [Submodule.pow_eq_span_pow_set]
    apply Submodule.span_le.mpr
    intro b hb
    obtain ⟨f, hf, heq⟩ := Set.mem_pow_iff_prod.mp hb
    let g (i : Fin n) : I := ⟨f i, hf i⟩
    change monomial 1 b ∈ (P.restrictScalars R).map (reesAlgebra (I ^ n)).val.toLinearMap
    refine ⟨reesDegreeOne (I ^ n) (productCenterElement I n g), hprod g, ?_⟩
    change monomial 1 (∏ i, f i) = monomial 1 b
    exact congrArg (monomial 1) heq
  intro b
  obtain ⟨p, hp, heq⟩ := hspan b.2
  have hp' : p = reesDegreeOne (I ^ n) b := Subtype.ext heq
  rw [hp'] at hp
  exact hp

/--
概要：Bl_{I^n} は a ∈ I の純冪 a^n に対応する標準チャートで被覆される。
方針：被覆に入らない斉次素イデアルは全ての次数一元を含み、Proj の被覆性に反する。
規約：KST §5、(5.10)。n は正で、中心の有限生成性は不要。
使われ方：冪比較のチャート同型を貼り合わせる。
-/
theorem iSup_affineBlowup_powerCharts (n : ℕ) (hn : 0 < n) :
    ⨆ a : I, affineBlowupChart (I ^ n) (powerCenterElement I a n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  by_contra hnot
  have hP (a : I) : reesDegreeOne (I ^ n) (powerCenterElement I a n) ∈
      x.asHomogeneousIdeal.toIdeal := by
    by_contra ha
    exact hnot (TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩)
  let : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hall := prime_contains_degreeOne_of_contains_powers I n hn x.asHomogeneousIdeal.toIdeal hP
  have htop : x ∈ (⊤ : (affineBlowup (I ^ n)).Opens) := trivial
  rw [← iSup_affineBlowupChart (I ^ n)] at htop
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  exact hb (hall b)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
