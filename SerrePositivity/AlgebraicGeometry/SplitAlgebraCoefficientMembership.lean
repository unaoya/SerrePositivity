module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientIdeal
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の係数による拡大イデアルの所属判定。
方針：一方向は生成元の帰納法、逆方向は分裂の射影と有限台の展開を使う。
規約：代数の自由な直和への分裂を明示的に入力する。
使われ方：基底上の係数中心とファイバー内の元のイデアルを照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {ι : Type*}
  (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
  (hpe : p.comp e = LinearMap.id)

include p hpe

/--
概要：拡大イデアルへの元の所属は、その全係数が元のイデアルに属することと同値。
方針：拡大イデアルの生成元で一方向を証明し、分裂の射影で係数展開を元に戻す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、イデアルの素性や有限生成性は不要。
使われ方：ファイバー上で消える元の判定と中心の admissible 性。
-/
theorem splitAlgebra_mem_map_iff (I : Ideal R) (x : B) :
    x ∈ I.map (algebraMap R B) ↔ ∀ i, e x i ∈ I := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro i
      have h : algebraMap R B r = r • (1 : B) := Algebra.algebraMap_eq_smul_one r
      rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    | zero => simp
    | add x y _ _ hx hy =>
      intro i
      simpa only [map_add, Finsupp.add_apply] using I.add_mem (hx i) (hy i)
    | smul b y _ hy => exact splitAlgebra_mul_coeff_mem e p hpe I b y hy
  · intro hx
    have hpx : p (e x) = x := LinearMap.congr_fun hpe x
    have hsum : x = ∑ i ∈ (e x).support, e x i • p (Finsupp.single i 1) := by
      calc
        x = p ((e x).sum fun i r => Finsupp.single i r) := by
          rw [Finsupp.sum_single, hpx]
        _ = ∑ i ∈ (e x).support, e x i • p (Finsupp.single i 1) := by
          simp only [Finsupp.sum, map_sum, ← map_smul, Finsupp.smul_single,
            smul_eq_mul, mul_one]
    rw [hsum]
    apply (I.map (algebraMap R B)).sum_mem
    intro i _
    simpa only [Algebra.smul_def] using
      (I.map (algebraMap R B)).mul_mem_right (p (Finsupp.single i 1))
        (Ideal.mem_map_of_mem _ (hx i))

/--
概要：代数イデアルが基底の拡大イデアルに含まれることは、係数イデアルの包含と同値。
方針：各元の所属判定と係数イデアルの普遍性を組み合わせる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基底と代数のイデアルを区別する。
使われ方：ファイバー上での非消滅から係数中心の補開集合を判定する。
-/
theorem splitAlgebraCoefficientIdeal_le_iff (J : Ideal B) (I : Ideal R) :
    splitAlgebraCoefficientIdeal e J ≤ I ↔ J ≤ I.map (algebraMap R B) := by
  rw [splitAlgebraCoefficientIdeal, finsuppCoefficientIdeal_le_iff]
  constructor
  · intro h x hx
    exact (splitAlgebra_mem_map_iff e p hpe I x).mpr (h (e x) ⟨x, hx, rfl⟩)
  · rintro h y ⟨x, hx, rfl⟩
    exact (splitAlgebra_mem_map_iff e p hpe I x).mp (h hx)

/--
概要：係数イデアルは自由な直和の分裂表示の選択によらない。
方針：両表示の係数イデアルを拡大イデアルの包含判定によって相互に比較する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、二つの直和の添字集合は異なってよい。
使われ方：局所的な自由表示の選択によらない平坦化中心の係数計算。
-/
theorem splitAlgebraCoefficientIdeal_eq {κ : Type*}
    (e' : B →ₗ[R] (κ →₀ R)) (p' : (κ →₀ R) →ₗ[R] B)
    (hpe' : p'.comp e' = LinearMap.id) (J : Ideal B) :
    splitAlgebraCoefficientIdeal e J = splitAlgebraCoefficientIdeal e' J := by
  apply le_antisymm
  · exact (splitAlgebraCoefficientIdeal_le_iff e p hpe J _).mpr
      ((splitAlgebraCoefficientIdeal_le_iff e' p' hpe' J _).mp le_rfl)
  · exact (splitAlgebraCoefficientIdeal_le_iff e' p' hpe' J _).mpr
      ((splitAlgebraCoefficientIdeal_le_iff e p hpe J _).mp le_rfl)

/--
概要：境界外の全素点で元のイデアルが消えなければ、係数イデアルは境界元の一つの冪を含む。
方針：係数イデアルの包含判定と根基の素イデアルによる記述を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、非包含は拡大された素イデアルについて述べる。
使われ方：有限生成係数中心が境界外を避けることを証明する。
-/
theorem exists_pow_mem_splitAlgebraCoefficientIdeal (J : Ideal B) (f : R)
    (hJ : ∀ q : Ideal R, q.IsPrime → f ∉ q → ¬ J ≤ q.map (algebraMap R B)) :
    ∃ n : ℕ, f ^ n ∈ splitAlgebraCoefficientIdeal e J := by
  have hf : f ∈ (splitAlgebraCoefficientIdeal e J).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    intro q hq
    by_contra hfq
    exact hJ q hq.2 hfq ((splitAlgebraCoefficientIdeal_le_iff e p hpe J q).mp hq.1)
  exact hf

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
