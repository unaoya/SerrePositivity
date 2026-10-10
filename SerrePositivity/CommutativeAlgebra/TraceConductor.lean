module

public import SerrePositivity.CommutativeAlgebra.SeparableBaseChange
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# トレース双対基底による共通分母

正規な整域 `R` の分数体 `K` の有限分離拡大 `L` を考える。
基底のトレース双対を整元にする分母 `g` は、`R` 上整な全ての元を
元の基底の `R` 線形包へ送る。トレースの整性と `R` の正規性により
基底展開の係数が `R` に入ることが証明の要点である。
有限分離拡大の基底を完全な純非分離拡大へ移す結果にも接続し、元の基底から分母を得る。
定理2.5の共通分母の議論の一般論であり、塔や正規化長さには依存しない。
-/

public section
universe u
namespace SerrePositivity

variable (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type u} [Finite ι] [DecidableEq ι]

/-- 双対基底を整元にする分母は、任意の整元を元の基底の線形包へ送る。
整元のトレースが分数体内で整であることと、底環の正規性を使う。 -/
theorem smul_mem_span_of_integral_traceDual (b : Module.Basis ι K L) (g : R)
    (hg : ∀ i, IsIntegral R (g • b.traceDual i))
    {x : L} (hx : IsIntegral R x) :
    g • x ∈ Submodule.span R (Set.range b) := by
  rw [b.mem_span_iff_repr_mem R]
  intro i
  have hr : b.repr (g • x) i = Algebra.trace K L ((g • x) * b.traceDual i) := by
    simpa only [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply] using
      b.traceDual.traceDual_repr_apply (g • x) i
  rw [hr]
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  have hm : (g • x) * b.traceDual i = (g • b.traceDual i) * x := by
    simp only [Algebra.smul_def]
    ring
  rw [hm]
  exact Algebra.isIntegral_trace ((hg i).mul hx)

omit [DecidableEq ι] in
/-- 有限個の双対基底の共通分母を選べば、整閉包全体を同時に線形包へ送れる。
分母の存在には Mathlib の有限個の代数的元の整倍数の定理を使う。 -/
theorem exists_smul_integral_mem_span
    (b : Module.Basis ι K L) :
    ∃ g : R, g ≠ 0 ∧ ∀ x : L, IsIntegral R x →
      g • x ∈ Submodule.span R (Set.range b) := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  let : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.trans R K L
  obtain ⟨g, hg, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples R
    (Finset.univ.image b.traceDual)
  refine ⟨g, hg, fun x hx ↦ smul_mem_span_of_integral_traceDual R K L b g ?_ hx⟩
  intro i
  exact hi _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

omit [DecidableEq ι] in
/-- 共通分母をより小さい環 `A` から選ぶ形。
双対基底の元が `A` 上代数的なら、有限個の整倍数の共通分母を `A` 内で取れる。
底環 `R` への拡大後も整性は保たれるので、同じ分母が `R` 上の整元全てに使える。 -/
theorem exists_smul_integral_mem_span_of_algebraic
    (A : Type u) [CommRing A] [IsDomain A] [Algebra A R] [Algebra A L]
    [IsScalarTower A R L] [Algebra.IsAlgebraic A L]
    (b : Module.Basis ι K L) :
    ∃ g : A, g ≠ 0 ∧ ∀ x : L, IsIntegral R x →
      g • x ∈ Submodule.span R (Set.range b) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨g, hg, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples A
    (Finset.univ.image b.traceDual)
  refine ⟨g, hg, fun x hx ↦ ?_⟩
  have hd : ∀ i, IsIntegral R (algebraMap A R g • b.traceDual i) := by
    intro i
    rw [IsScalarTower.algebraMap_smul]
    exact (hi _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).tower_top
  simpa only [IsScalarTower.algebraMap_smul] using
    smul_mem_span_of_integral_traceDual R K L b (algebraMap A R g) hd hx

omit [DecidableEq ι] in
/-- 基底を含む部分代数に対する共通分母。
`C` の全ての元が `R` 上整なら、一つの非零分母で `C` 全体を `B` に送れる。
分母は小さい環 `A` 内に取るため、論文の `g ∈ A` という条件を保てる。 -/
theorem exists_smul_subalgebra_le_of_integral
    (A : Type u) [CommRing A] [IsDomain A] [Algebra A R] [Algebra A L]
    [IsScalarTower A R L] [Algebra.IsAlgebraic A L]
    (b : Module.Basis ι K L) (B C : Subalgebra R L)
    (hb : ∀ i, b i ∈ B) (hC : ∀ x ∈ C, IsIntegral R x) :
    ∃ g : A, g ≠ 0 ∧ ∀ x ∈ C, g • x ∈ B := by
  classical
  obtain ⟨g, hg, hx⟩ := exists_smul_integral_mem_span_of_algebraic R K L A b
  refine ⟨g, hg, fun x hxc ↦ ?_⟩
  have hspan : Submodule.span R (Set.range b) ≤ B.toSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  exact hspan (hx x (hC x hxc))

/-- 有限分離拡大の基底を完全な純非分離拡大へ移して、共通分母を構成する。
共通の体 `Ω` の基底を別途仮定する必要はなく、元の `L/K` の基底が `B` に入ればよい。
正規性・整性・小さい環上の代数性は、それぞれ明示的に要求する。 -/
theorem exists_smul_subalgebra_le_of_perfectBaseChange
    (A R K E L Ω : Type u) [CommRing A] [IsDomain A]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    [FiniteDimensional K L] [PerfectField E] [IsPurelyInseparable L Ω]
    [Algebra R E] [IsFractionRing R E] [Algebra R Ω] [IsScalarTower R E Ω]
    [Algebra A R] [Algebra A Ω] [IsScalarTower A R Ω] [Algebra.IsAlgebraic A Ω]
    (p : ℕ) [ExpChar K p] {ι : Type u} [Finite ι]
    (b : Module.Basis ι K L) (B C : Subalgebra R Ω)
    (hb : ∀ i, algebraMap L Ω (b i) ∈ B) (hC : ∀ x ∈ C, IsIntegral R x) :
    ∃ g : A, g ≠ 0 ∧ ∀ x ∈ C, g • x ∈ B := by
  let e := tensorProductEquiv_of_perfect_of_purelyInseparable K E L Ω p
  let : Module.Finite E Ω := Module.Finite.of_surjective e.toLinearMap e.surjective
  apply exists_smul_subalgebra_le_of_integral R E Ω A
    (basisOfPerfectBaseChange K E L Ω p b) B C _ hC
  intro i
  simpa only [basisOfPerfectBaseChange_apply] using hb i

/-- 代数的な整域拡大の分数体から基底を選び、完全な係数拡大後の共通分母を得る。
`D` の像を含む `B` に対し、基底の選択も証明内で行う。
分数体拡大の有限次元性も、有限加群の仮定から導く。
利用側は基底やその包含を用意せず、環の包含と整性を与えればよい。 -/
theorem exists_smul_subalgebra_le_of_fractionRing
    (A D R K E L Ω : Type u) [CommRing A] [IsDomain A]
    [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field E] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    [PerfectField E] [IsPurelyInseparable L Ω]
    [Algebra R E] [IsFractionRing R E] [Algebra R Ω] [IsScalarTower R E Ω]
    [Algebra A R] [Algebra A Ω] [IsScalarTower A R Ω] [Algebra.IsAlgebraic A Ω]
    [Algebra D Ω] [IsScalarTower D L Ω]
    (p : ℕ) [ExpChar K p] (B C : Subalgebra R Ω)
    (hD : ∀ d : D, algebraMap D Ω d ∈ B) (hC : ∀ x ∈ C, IsIntegral R x) :
    ∃ g : A, g ≠ 0 ∧ ∀ x ∈ C, g • x ∈ B := by
  let := finiteDimensional_fractionRing_of_finite A D K L
  obtain ⟨s, b, hb⟩ := exists_basis_fractionRing_mem_range A D K L
  let : Finite s := Module.Finite.finite_basis b
  apply exists_smul_subalgebra_le_of_perfectBaseChange A R K E L Ω p b B C _ hC
  intro i
  obtain ⟨d, hd⟩ := hb i
  rw [← hd, ← IsScalarTower.algebraMap_apply D L Ω]
  exact hD d

end SerrePositivity
