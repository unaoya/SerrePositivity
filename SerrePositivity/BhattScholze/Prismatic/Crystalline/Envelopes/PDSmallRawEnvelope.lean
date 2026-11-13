module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRelativeFree
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# 小さい多項式分冪模型の普遍性

## 概要
第零頂点の多項式環と頂点差の自由分冪代数のテンソル積が、
`(k/J)[X]` への枠の相対分冪包となることを示す。

## 方針
第零頂点への代入と頂点差の線形延長で標的への射を作る。
枠の核は、係数の `J` を零にし各頂点を第零頂点と同一視すると消える。

## 規約
係数の p 進完備性から p 局所性を得る。係数の p 正則性を明示する。

## 使われ方
BS 著者版 Theorem 5.2 の小さい分冪 Čech 模型の同定。
-/

public noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic
namespace PDSmallRawEnvelope

variable {k : Type u} [CommRing k] {J : Ideal k}
variable (p : ℕ) [Fact p.Prime] (r n : ℕ) (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hreg : Function.Injective (fun x : k => (p : k) * x))

local notation "Coeff" => MvPolynomial (Fin r) k
local notation "CoeffQ" => Localization.Away (p : Coeff)
local notation "DiffVars" => Fin r × Fin n
local notation "Raw" => pdRaw k r n
local notation "Vars" => ULift (Fin r)
local notation "Frame" => pdFrame k Vars n
local notation "Residue" => MvPolynomial (Fin r) (k ⧸ J)
local notation "evaluate" => pdFrameEval (k := k)
  (fun j : Vars => (MvPolynomial.X (ULift.down j) : Residue)) n
local notation "KerEval" => RingHom.ker evaluate

include hk in
private theorem isUnit_natCast_of_not_dvd (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : k) := by
  let := hk
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm
  have he : IsCoprime (p : k) (m : k) := by
    simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom k)
  obtain ⟨a, b, h⟩ := he
  have hmem : b * (m : k) - 1 ∈ Ideal.jacobson (⊥ : Ideal k) := by
    have h' : b * (m : k) - 1 = -(a * (p : k)) := by rw [← h]; ring
    rw [h']
    apply (Ideal.jacobson (⊥ : Ideal k)).neg_mem
    apply Ideal.mul_mem_left
    exact IsAdicComplete.le_jacobson_bot (Ideal.span {(p : k)})
      (Ideal.mem_span_singleton_self _)
  exact isUnit_of_mul_isUnit_right (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hmem)

include hk in
private theorem polynomial_local (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : Coeff) := by
  simpa only [map_natCast] using (isUnit_natCast_of_not_dvd p hk m hm).map (algebraMap k Coeff)

omit [Fact p.Prime] in
include hreg in
private theorem polynomial_regular : IsRegular (p : Coeff) := by
  have h : IsSMulRegular Coeff (p : Coeff) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular k (p : k) from hreg).of_flat (S := Coeff)
  exact ⟨h, fun x y hxy => h (by
    change (p : Coeff) * x = (p : Coeff) * y
    simpa only [mul_comm (p : Coeff)] using hxy)⟩

omit [Fact p.Prime] in
include hreg in
private theorem localization_injective : Function.Injective (algebraMap Coeff CoeffQ) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : Coeff)) (S := CoeffQ)).mpr
  rintro ⟨x, m, rfl⟩
  exact (polynomial_regular p r hreg).pow m

@[instance_reducible] private def rationalAlgebra (hk : IsAdicComplete (Ideal.span {(p : k)}) k) :
    Algebra ℚ CoeffQ :=
  DeltaStructure.primeDividedPowersAwayRatAlgebra (polynomial_local p r hk)

/-- 頂点差と基底の分冪を含む小さい模型の分冪イデアル。 -/
abbrev ideal : Ideal Raw := PDRelativeFree.ideal Coeff DiffVars J

/-- 小さい模型の分冪構造。 -/
def dividedPowers : DividedPowers (A := Raw) (ideal (k := k) (J := J) r n) :=
  let := rationalAlgebra p r hk
  PDRelativeFree.dividedPowers Coeff DiffVars CoeffQ (localization_injective p r hreg) γ

/-- 枠の変数を第零頂点の変数と頂点差の和へ送る標準脚。 -/
def unit : Frame →ₐ[k] Raw := MvPolynomial.aeval (fun x => copy k r ⦋n⦌ x.1.down x.2)

@[simp] private theorem unit_X (i : Vars × Fin (n + 1)) :
    unit r n (MvPolynomial.X i) = copy k r ⦋n⦌ i.1.down i.2 :=
  MvPolynomial.aeval_X _ _

private theorem kernel_le {E : Type*} [CommSemiring E] [Algebra k E] (f : Frame →ₐ[k] E)
    (hbase : ∀ a ∈ J, algebraMap k E a = 0)
    (hcopy : ∀ j i, f (MvPolynomial.X (j, i)) = f (MvPolynomial.X (j, 0))) :
    KerEval ≤ RingHom.ker f := by
  let g : Residue →+* E :=
    MvPolynomial.eval₂Hom (Ideal.Quotient.lift J (algebraMap k E) hbase)
      (fun j => f (MvPolynomial.X (ULift.up j, 0)))
  have hf : f.toRingHom = g.comp (evaluate).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change f (MvPolynomial.C a) = g (evaluate (MvPolynomial.C a))
      have he : evaluate (MvPolynomial.C a) = MvPolynomial.C (Ideal.Quotient.mk J a) := by
        exact (evaluate).commutes a
      rw [he, ← MvPolynomial.algebraMap_eq, f.commutes]
      simp [g]
    · intro x
      change f (MvPolynomial.X x) = g (evaluate (MvPolynomial.X x))
      rw [pdFrameEval_X]
      simpa [g] using hcopy x.1 x.2
  intro x hx
  have hx' := RingHom.mem_ker.mp hx
  change f.toRingHom x = 0
  rw [hf, RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
  exact (congrArg g hx').trans (map_zero g)

set_option backward.isDefEq.respectTransparency false in
private theorem unit_map_le :
    (KerEval).map (unit (k := k) r n) ≤ ideal (k := k) (J := J) r n := by
  let d (j : Vars × Fin n) : Frame :=
    MvPolynomial.X (j.1, j.2.succ) - MvPolynomial.X (j.1, 0)
  let G : Set Frame := MvPolynomial.C '' (J : Set k) ∪ Set.range d
  let I : Ideal Frame := Ideal.span G
  let f : Frame →ₐ[k] (Frame ⧸ I) := Ideal.Quotient.mkₐ k I
  have hbase (a : k) (ha : a ∈ J) : algebraMap k (Frame ⧸ I) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩))
  have hcopy (j : Vars) (i : Fin (n + 1)) :
      f (MvPolynomial.X (j, i)) = f (MvPolynomial.X (j, 0)) := by
    refine Fin.cases rfl (fun i => ?_) i
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨(j, i), rfl⟩))
  have h := kernel_le (J := J) r n (E := Frame ⧸ I) f hbase hcopy
  rw [Ideal.map_le_iff_le_comap]
  apply (show KerEval ≤ I from fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (h hx)).trans
  apply Ideal.span_le.mpr
  intro x hx
  change unit (k := k) r n x ∈ ideal (k := k) (J := J) r n
  rcases hx with ⟨a, ha, rfl⟩ | ⟨⟨j, i⟩, rfl⟩
  · rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact PDRelativeFree.coefficient_mem Coeff DiffVars ha
  · change unit r n (MvPolynomial.X (j, i.succ) - MvPolynomial.X (j, 0)) ∈ _
    rw [map_sub, unit_X, unit_X, copy, copy, show vertexDiff k r ⦋n⦌ j.down 0 = 0 from rfl,
      map_zero, add_zero, add_sub_cancel_left]
    exact PDRelativeFree.dp_mem Coeff DiffVars 1 one_ne_zero _

variable {E : Type u} [CommRing E] [Algebra k E] {I' : Ideal E}
variable (ε : DividedPowers I')
variable (f : pdFrame k (ULift.{u} (Fin r)) n →ₐ[k] E)
variable (hf : (RingHom.ker (pdFrameEval (k := k)
  (fun j : ULift.{u} (Fin r) => (MvPolynomial.X j.down : MvPolynomial (Fin r) (k ⧸ J))) n)).map f
    ≤ I')

private def targetLeft : Coeff →ₐ[k] E :=
  MvPolynomial.aeval fun j => f (MvPolynomial.X (ULift.up j, 0))

private def targetDiff : (DiffVars →₀ k) →ₗ[k] E :=
  Finsupp.linearCombination k fun x =>
    f (MvPolynomial.X (ULift.up x.1, x.2.succ)) - f (MvPolynomial.X (ULift.up x.1, 0))

include hf in
private theorem targetDiff_mem (x : DiffVars →₀ k) : targetDiff r n f x ∈ I' := by
  classical
  rw [targetDiff, Finsupp.linearCombination_apply]
  apply I'.sum_mem
  intro j hj
  dsimp only
  rw [Algebra.smul_def, ← map_sub]
  apply I'.mul_mem_left
  apply hf
  apply Ideal.mem_map_of_mem
  change evaluate (MvPolynomial.X (ULift.up j.1, j.2.succ) - MvPolynomial.X (ULift.up j.1, 0)) = 0
  rw [map_sub, pdFrameEval_X, pdFrameEval_X, sub_self]

include hf in
private theorem targetDiff_vertex (j : Fin r) (i : Fin (n + 1)) :
    (PDRelativeFree.lift Coeff DiffVars ε
      (targetLeft r n f) (targetDiff r n f) (targetDiff_mem r n f hf))
      (copy k r ⦋n⦌ j i) = f (MvPolynomial.X (ULift.up j, i)) := by
  let F := PDRelativeFree.lift Coeff DiffVars ε
    (targetLeft r n f) (targetDiff r n f) (targetDiff_mem r n f hf)
  change F (baseVar k r ⦋n⦌ j + pdDiff k r ⦋n⦌ (vertexDiff k r ⦋n⦌ j i)) = _
  have hleft : F (baseVar k r ⦋n⦌ j) = f (MvPolynomial.X (ULift.up j, 0)) := by
    unfold F baseVar
    rw [PDRelativeFree.lift_includeLeft, targetLeft, MvPolynomial.aeval_X]
  have hright : ∀ x : DiffVars →₀ k, F (pdDiff k r ⦋n⦌ x) = targetDiff r n f x := by
    intro x
    change F (PDRelativeFree.generator Coeff DiffVars 1 x) = _
    dsimp only [F]
    rw [PDRelativeFree.lift_generator_apply, ε.dpow_one (targetDiff_mem r n f hf x)]
  rw [map_add, hleft, hright]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [vertexDiff]
  · simp [vertexDiff, targetDiff, Finsupp.linearCombination_single]

include hk hreg in
private theorem hom_ext {g₁ g₂ : Raw →ₐ[k] E}
    (h₁ : (dividedPowers p r n γ hk hreg).IsDPMorphism ε g₁.toRingHom)
    (h₂ : (dividedPowers p r n γ hk hreg).IsDPMorphism ε g₂.toRingHom)
    (he : g₁.comp (unit r n) = g₂.comp (unit r n)) : g₁ = g₂ := by
  let := rationalAlgebra p r hk
  have hcopy j i : g₁ (copy k r ⦋n⦌ j i) = g₂ (copy k r ⦋n⦌ j i) := by
    have h := DFunLike.congr_fun he (MvPolynomial.X (ULift.up j, i))
    simpa only [AlgHom.comp_apply, unit_X] using h
  have hbase j : g₁ (baseVar k r ⦋n⦌ j) = g₂ (baseVar k r ⦋n⦌ j) := by
    simpa only [copy, vertexDiff, Fin.cases_zero, map_zero, add_zero] using hcopy j 0
  apply Algebra.TensorProduct.ext
  · exact MvPolynomial.algHom_ext hbase
  · apply DividedPowerAlgebra.algHom_ext
    intro m x
    have hlin : g₁.toLinearMap.comp (pdDiff k r ⦋n⦌) = g₂.toLinearMap.comp (pdDiff k r ⦋n⦌) := by
      apply (Finsupp.basisSingleOne (R := k)).ext
      rintro ⟨j,i⟩
      change g₁ (pdDiff k r ⦋n⦌ (Finsupp.single (j, i) 1)) =
        g₂ (pdDiff k r ⦋n⦌ (Finsupp.single (j, i) 1))
      have h := hcopy j i.succ
      simpa only [copy, map_add, hbase, vertexDiff, Fin.cases_succ, add_right_inj] using h
    have hdp := PDRelativeFree.dividedPowers_dp_one Coeff DiffVars
      CoeffQ (localization_injective p r hreg) γ m x
    have hm := PDRelativeFree.dp_mem Coeff DiffVars (J := J) 1 one_ne_zero x
    change g₁.toRingHom (PDRelativeFree.generator Coeff DiffVars m x) =
      g₂.toRingHom (PDRelativeFree.generator Coeff DiffVars m x)
    rw [← hdp]
    change g₁.toRingHom ((dividedPowers p r n γ hk hreg).dpow m _) =
      g₂.toRingHom ((dividedPowers p r n γ hk hreg).dpow m _)
    rw [h₁.map_dpow hm, h₂.map_dpow hm]
    exact congrArg (ε.dpow m) (DFunLike.congr_fun hlin x)

/-- 小さい未完備模型は、基底の分冪と両立する相対分冪包。 -/
theorem isRelativePDEnvelope :
    IsRelativePDEnvelope γ KerEval (D := Raw)
      (dividedPowers p r n γ hk hreg) (unit (k := k) r n) where
  map_le := unit_map_le r n
  base_dp := by
    let := rationalAlgebra p r hk
    exact PDRelativeFree.base_isDPMorphism Coeff DiffVars CoeffQ (localization_injective p r hreg) γ
  lift ε f hf he := by
    let := rationalAlgebra p r hk
    let G := PDRelativeFree.lift Coeff DiffVars ε
      (targetLeft r n f) (targetDiff r n f) (targetDiff_mem r n f hf)
    have hG := PDRelativeFree.lift_isDPMorphism Coeff DiffVars CoeffQ
      (localization_injective p r hreg) γ ε
      (targetLeft r n f) (targetDiff r n f) (targetDiff_mem r n f hf) he
    have hGc : G.comp (unit r n) = f := by
      apply MvPolynomial.algHom_ext
      rintro ⟨j,i⟩
      change G (unit r n (MvPolynomial.X (j, i))) = f (MvPolynomial.X (j, i))
      rw [unit_X]
      exact targetDiff_vertex r n ε f hf j.down i
    exact ⟨G, ⟨hG, hGc⟩, fun g hg => hom_ext p r n γ hk hreg ε hg.1 hG (hg.2.trans hGc.symm)⟩

omit [Fact p.Prime] in
include hreg in
/-- 係数が p 正則なら、小さい未完備模型も p 正則。 -/
theorem raw_regular : IsSMulRegular Raw (p : Raw) := by
  intro x y h
  apply (pdRawBasis k r n).repr.injective
  apply Finsupp.ext
  intro m
  apply hreg
  change (p : Raw) * x = (p : Raw) * y at h
  rw [← map_natCast (algebraMap k Raw), ← Algebra.smul_def, ← Algebra.smul_def] at h
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
    congrArg (fun z => (pdRawBasis k r n).repr z m) h

set_option backward.isDefEq.respectTransparency false in
include hk hreg in
/-- 頂点の添字写像は小さい未完備模型の分冪を保つ。 -/
private theorem map_isDPMorphism {m l : SimplexCategory} (θ : m ⟶ l) :
    (dividedPowers p r m.len γ hk hreg).IsDPMorphism (dividedPowers p r l.len γ hk hreg)
      (pdRawMap k r θ).toRingHom := by
  let := rationalAlgebra p r hk
  let δ : DividedPowers (A := pdRaw k r l.len) (ideal (k := k) (J := J) r l.len) :=
    dividedPowers p r l.len γ hk hreg
  let v : (Fin r × Fin m.len →₀ k) →ₗ[k] pdRaw k r l.len := (pdDiff k r l).comp (diffMap k r θ)
  have hv (x : Diff k r m) : v x ∈ ideal (k := k) (J := J) r l.len :=
    PDRelativeFree.dp_mem Coeff (Fin r × Fin l.len) 1 one_ne_zero _
  let f : Coeff →ₐ[k] pdRaw k r l.len := MvPolynomial.aeval fun j => copy k r l j (θ.toOrderHom 0)
  let G := PDRelativeFree.lift (A := k) Coeff (Fin r × Fin m.len)
    (E := pdRaw k r l.len) (DPideal' := ideal (k := k) (J := J) r l.len) δ f v hv
  have hG : G = pdRawMap k r θ := by
    apply Algebra.TensorProduct.ext
    · apply MvPolynomial.algHom_ext
      intro j
      change G ((includeLeft : Coeff →ₐ[k] pdRaw k r m.len) (MvPolynomial.X j)) = _
      rw [PDRelativeFree.lift_includeLeft]
      dsimp only [f]
      rw [MvPolynomial.aeval_X]
      exact (pdRawMap_baseVar k r θ j).symm
    · change G.comp (includeRight : DividedPowerAlgebra k (Diff k r m) →ₐ[k] _) =
        (pdRawMap k r θ).comp includeRight
      apply DividedPowerAlgebra.algHom_ext (R := k) (M := Diff k r m) (A := pdRaw k r l.len)
      intro a x
      change G (PDRelativeFree.generator Coeff (Fin r × Fin m.len) a x) =
        pdRawMap k r θ (PDRelativeFree.generator Coeff (Fin r × Fin m.len) a x)
      rw [PDRelativeFree.lift_generator_apply]
      have h := DFunLike.congr_fun (pdRawMap_right k r θ) (DividedPowerAlgebra.dp k a x)
      change pdRawMap k r θ (PDRelativeFree.generator Coeff (Fin r × Fin m.len) a x) =
        includeRight (DividedPowerAlgebra.map k (diffMap k r θ) (DividedPowerAlgebra.dp k a x)) at h
      rw [h, DividedPowerAlgebra.map_apply_dp]
      exact PDRelativeFree.dividedPowers_dp_one Coeff (Fin r × Fin l.len)
        CoeffQ (localization_injective p r hreg) γ a _
  change (dividedPowers p r m.len γ hk hreg).IsDPMorphism δ (pdRawMap k r θ).toRingHom
  rw [← hG]
  exact PDRelativeFree.lift_isDPMorphism Coeff (Fin r × Fin m.len) CoeffQ
    (localization_injective p r hreg) γ (E := pdRaw k r l.len)
    (DPideal' := ideal (k := k) (J := J) r l.len) δ f v hv
    (PDRelativeFree.base_isDPMorphism Coeff (Fin r × Fin l.len) CoeffQ
      (localization_injective p r hreg) γ)

/-- 未完備模型の添字写像は枠の標準脚と可換。 -/
private theorem map_unit {m l : SimplexCategory} (θ : m ⟶ l) (x : Vars × Fin (m.len + 1)) :
    pdRawMap k r θ (unit (k := k) r m.len (MvPolynomial.X x)) =
      unit (k := k) r l.len (MvPolynomial.X (x.1, θ.toOrderHom x.2)) := by
  rw [unit_X, unit_X]
  exact pdRawMap_copy k r θ x.1.down x.2

end PDSmallRawEnvelope
end SerrePositivity.BhattScholze.Prismatic
