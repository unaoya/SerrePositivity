module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.AlgebraTower
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import Mathlib.Algebra.Polynomial.Monic
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.FaithfullyFlatDerivedHomology
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction

/-!
# 一変数の分冪多項式代数 Γ_A⟨x⟩

## 概要
任意の係数環上の一元分冪代数の基底 γ_n とその底変換・普遍性、p 局所・p 正則な環上の基底と p 正則性、p = 0 の係数環上の次数ブロック基底と A[x]/(x^p) 上の自由性（切断多項式作用）、分冪添加環の底変換・係数射の平坦性・自由性、導来係数拡大の Koszul 判定・因子化・相対平坦性、標数 p の導来完備化、具体的評価環の導来比較と B/(y^p) からの自由・忠実平坦な射。

## 方針
BS 著者版 Lemma 2.38 の比較に用いる、一変数の分冪代数の一般論。
BS 著者版 Lemma 2.38 の証明の標準計算と Lemma 2.43 の標数 p での計算にあたる。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/PowerRootEnvelope/DividedPowerPrime`、`Delta/DividedPower/Principal/PrincipalDP`、`CommutativeAlgebra/DividedPowers/FreeDPModPBlocks`。
-/

universe u v

/-! ## 一元分冪代数の標準テンソル基底変更射

任意係数上の比較射と生成元公式を、基底の構成から独立に定める。
-/

@[expose] public noncomputable section RankOneDPBaseChangeMap

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 基底係数の拡大と既存分冪代数のmapから得られる実テンソル比較射。 -/
def rankOneDPBaseChangeMap :
    B ⊗[A] DividedPowerAlgebra A A →ₐ[B] DividedPowerAlgebra B B :=
  Algebra.TensorProduct.lift (Algebra.ofId B (DividedPowerAlgebra B B))
    (DividedPowerAlgebra.map B (Algebra.linearMap A B)) (fun _ _ ↦ Commute.all _ _)

/-- 実比較射のすべての純テンソル上の式。 -/
theorem rankOneDPBaseChangeMap_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeMap (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

/-- 標準分冪基底の純テンソルは拡大後の標準分冪基底へ写る。 -/
theorem rankOneDPBaseChangeMap_dp (n : ℕ) :
    rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) := by
  rw [rankOneDPBaseChangeMap_tmul, map_one, one_mul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one]

end SerrePositivity.BhattScholze

end RankOneDPBaseChangeMap

/-! ## 任意係数への一元分冪テンソル族の関係式

p正則性・p局所性を仮定せず、既存分冪代数の基底変更の逆射に必要な式を証明する。
-/

@[expose] public noncomputable section RankOneDPTensorRelations

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 既存分冪代数のテンソル内の、b^n⊗γ_n(1)という実族。 -/
def rankOneDPTensorValue (n : ℕ) (b : B) : B ⊗[A] DividedPowerAlgebra A A :=
  (b ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A)

/-- 具体的テンソル族の零次関係。 -/
theorem rankOneDPTensorValue_zero (b : B) : rankOneDPTensorValue (A := A) 0 b = 1 := by
  rw [rankOneDPTensorValue, pow_zero, DividedPowerAlgebra.dp_zero,
    ← Algebra.TensorProduct.one_def]

/-- 具体的テンソル族の全スカラー関係。 -/
theorem rankOneDPTensorValue_smul (n : ℕ) (r b : B) :
    rankOneDPTensorValue (A := A) n (r • b) = r ^ n • rankOneDPTensorValue (A := A) n b := by
  simp only [rankOneDPTensorValue, smul_eq_mul, mul_pow, TensorProduct.smul_tmul']

/-- 具体的テンソル族の同一元の全積関係。 -/
theorem rankOneDPTensorValue_mul (n m : ℕ) (b : B) :
    rankOneDPTensorValue (A := A) n b * rankOneDPTensorValue (A := A) m b =
      (n + m).choose n • rankOneDPTensorValue (A := A) (n + m) b := by
  rw [rankOneDPTensorValue, rankOneDPTensorValue, rankOneDPTensorValue,
    Algebra.TensorProduct.tmul_mul_tmul, ← pow_add, DividedPowerAlgebra.dp_mul,
    TensorProduct.tmul_smul]

/-- 二項展開による、具体的テンソル族の全加法関係。 -/
theorem rankOneDPTensorValue_add (n : ℕ) (b c : B) :
    rankOneDPTensorValue (A := A) n (b + c) =
      (Finset.antidiagonal n).sum (fun k ↦
        rankOneDPTensorValue (A := A) k.1 b * rankOneDPTensorValue (A := A) k.2 c) := by
  simp only [rankOneDPTensorValue]
  rw [(Commute.all b c).add_pow', TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  have hn : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
  rw [Algebra.TensorProduct.tmul_mul_tmul, DividedPowerAlgebra.dp_mul, hn,
    TensorProduct.tmul_smul]
  exact (TensorProduct.smul_tmul' (n.choose k.1) (b ^ k.1 * c ^ k.2)
    (DividedPowerAlgebra.dp A n (1 : A))).symm

end SerrePositivity.BhattScholze

end RankOneDPTensorRelations

/-! ## 任意係数への一元分冪代数の実テンソル基底変更

既存比較射の逆をlift'で具体的に構成する。係数環のねじれを制限しない。
-/

@[expose] public noncomputable section RankOneDPBaseChangeUniversal

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- γ_n(b)をb^n⊗γ_n(1)へ送る実逆射。 -/
def rankOneDPBaseChangeInverse :
    DividedPowerAlgebra B B →ₐ[B] B ⊗[A] DividedPowerAlgebra A A :=
  DividedPowerAlgebra.lift' (f := fun nm ↦ rankOneDPTensorValue (A := A) nm.1 nm.2)
    rankOneDPTensorValue_zero rankOneDPTensorValue_smul
    rankOneDPTensorValue_mul rankOneDPTensorValue_add

/-- 逆射の全分冪生成元上の具体的な式。 -/
theorem rankOneDPBaseChangeInverse_dp (n : ℕ) (b : B) :
    rankOneDPBaseChangeInverse (A := A) (DividedPowerAlgebra.dp B n b) =
      rankOneDPTensorValue (A := A) n b := by
  rw [rankOneDPBaseChangeInverse, DividedPowerAlgebra.lift'_apply_dp]

/-- 逆射は標準生成元を指定された純テンソルへ送る。 -/
theorem rankOneDPBaseChangeInverse_dp_one (n : ℕ) :
    rankOneDPBaseChangeInverse (A := A) (DividedPowerAlgebra.dp B n (1 : B)) =
      (1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A) := by
  rw [rankOneDPBaseChangeInverse_dp, rankOneDPTensorValue, one_pow]

/-- 実比較射と実逆射の合成は、拡大後の分冪代数上の恒等射。 -/
theorem rankOneDPBaseChangeMap_comp_inverse :
    (rankOneDPBaseChangeMap (A := A) (B := B)).comp rankOneDPBaseChangeInverse =
      AlgHom.id B (DividedPowerAlgebra B B) := by
  apply DividedPowerAlgebra.algHom_ext
  intro n b
  change rankOneDPBaseChangeMap
    (rankOneDPBaseChangeInverse (DividedPowerAlgebra.dp B n b)) = DividedPowerAlgebra.dp B n b
  rw [rankOneDPBaseChangeInverse_dp, rankOneDPTensorValue,
    rankOneDPBaseChangeMap_tmul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one]
  simpa only [smul_eq_mul, mul_one, Algebra.smul_def] using
    (DividedPowerAlgebra.dp_smul (R := B) (r := b) (n := n) (m := (1 : B))).symm

/-- 実逆射と実比較射の合成は、実テンソル代数上の恒等射。 -/
theorem rankOneDPBaseChangeInverse_comp_map :
    (rankOneDPBaseChangeInverse (A := A) (B := B)).comp rankOneDPBaseChangeMap =
      AlgHom.id B (B ⊗[A] DividedPowerAlgebra A A) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply DividedPowerAlgebra.algHom_ext
    intro n a
    change rankOneDPBaseChangeInverse
      (rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n a)) = _
    rw [rankOneDPBaseChangeMap_tmul, map_one, one_mul,
      DividedPowerAlgebra.map_apply_dp, rankOneDPBaseChangeInverse_dp]
    have ha : DividedPowerAlgebra.dp A n a = a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
      simpa only [smul_eq_mul, mul_one] using
        (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
    change ((algebraMap A B a) ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A) =
      (1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n a
    rw [ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [Algebra.smul_def, mul_one, map_pow]

/-- 任意の可換係数環に対する、既存実比較射を順射とする代数同型。 -/
def rankOneDPBaseChangeUniversalEquiv :
    B ⊗[A] DividedPowerAlgebra A A ≃ₐ[B] DividedPowerAlgebra B B :=
  AlgEquiv.ofAlgHom rankOneDPBaseChangeMap rankOneDPBaseChangeInverse
    rankOneDPBaseChangeMap_comp_inverse rankOneDPBaseChangeInverse_comp_map

/-- 一般基底変更同型の全純テンソル上の具体式。 -/
theorem rankOneDPBaseChangeUniversalEquiv_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeUniversalEquiv (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

/-- 一般基底変更同型の逆は全分冪生成元で指定されたテンソル族に一致する。 -/
theorem rankOneDPBaseChangeUniversalEquiv_symm_dp (n : ℕ) (b : B) :
    (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).symm
      (DividedPowerAlgebra.dp B n b) = rankOneDPTensorValue (A := A) n b :=
  rankOneDPBaseChangeInverse_dp n b

end SerrePositivity.BhattScholze

end RankOneDPBaseChangeUniversal

/-! ## 既存一元分冪代数の具体的基底

線形生成は任意の可換環で成立する。線形独立性にはℚ代数への単射を明示する。
-/

@[expose] public noncomputable section RankOneDPBasis

namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]

/-- 任意の可換環上の一元分冪代数は全γ_n(1)で線形生成される。 -/
theorem rankOneDP_span_eq_top :
    Submodule.span A (Set.range (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A))) = ⊤ := by
  let V := Submodule.span A (Set.range (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A)))
  apply top_unique
  intro f hf
  clear hf
  change f ∈ V
  induction f using DividedPowerAlgebra.induction_on with
  | C a =>
      have h0 : DividedPowerAlgebra.dp A 0 (1 : A) ∈ V :=
        Submodule.subset_span (Set.mem_range_self 0)
      simpa only [DividedPowerAlgebra.dp_zero, Algebra.smul_def, mul_one] using V.smul_mem a h0
  | add f g hf hg => exact V.add_mem hf hg
  | dp f n a hf =>
      have ha : DividedPowerAlgebra.dp A n a =
          a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
        simpa only [smul_eq_mul, mul_one] using
          (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
      rw [ha, mul_smul_comm]
      apply V.smul_mem
      induction hf using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨k, rfl⟩ := hz
          rw [DividedPowerAlgebra.dp_mul]
          have hmem : DividedPowerAlgebra.dp A (k + n) (1 : A) ∈ V :=
            Submodule.subset_span (Set.mem_range_self (k + n))
          exact nsmul_mem hmem _
      | zero => simpa only [zero_mul] using V.zero_mem
      | add x z hx hz ihx ihz => simpa only [add_mul] using V.add_mem ihx ihz
      | smul r z hz ih => simpa only [smul_mul_assoc] using V.smul_mem r ih

/-- 有理代数の多項式環への標準分冪評価。 -/
def rankOneDPPolynomialEval (A : Type u) [CommRing A] (C : Type v) [CommRing C]
    [Algebra A C] [Algebra ℚ C] : DividedPowerAlgebra A A →ₐ[A] Polynomial C := by
  classical
  exact DividedPowerAlgebra.lift
    (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (Polynomial C)))
    (LinearMap.toSpanSingleton A (Polynomial C) Polynomial.X)
    (by intro m; exact Submodule.mem_top)

/-- 標準評価はγ_n(1)を、係数環内の階乗逆数倍のX^nへ送る。 -/
theorem rankOneDPPolynomialEval_dp (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (n : ℕ) :
    rankOneDPPolynomialEval A C (DividedPowerAlgebra.dp A n (1 : A)) =
      Polynomial.C (Ring.inverse (n.factorial : C)) * Polynomial.X ^ n := by
  classical
  rw [rankOneDPPolynomialEval, DividedPowerAlgebra.lift_apply_dp,
    LinearMap.toSpanSingleton_apply_one, DividedPowers.RatAlgebra.dpow_apply,
    ite_eq_left (by trivial)]
  have hunit := IsUnit.natCast_factorial_of_algebra ℚ n (A := C)
  have hm := hunit.map_ringInverse Polynomial.C
  simp only [map_natCast] at hm
  rw [← hm]

/-- 有理代数への単射がある場合、全γ_n(1)は線形独立。 -/
theorem rankOneDP_linearIndependent (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) :
    LinearIndependent A (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a hs n hn
  have he := congrArg (fun z : Polynomial C ↦ z.coeff n)
    (congrArg (rankOneDPPolynomialEval A C) hs)
  have he' : algebraMap A C (a n) * Ring.inverse (n.factorial : C) = 0 := by
    simpa [map_sum, map_smul, rankOneDPPolynomialEval_dp, Polynomial.coeff_sum,
      Polynomial.coeff_smul, Polynomial.coeff_C_mul_X_pow, Algebra.smul_def, hn] using he
  have hem := congrArg (fun z : C ↦ z * (n.factorial : C)) he'
  rw [mul_assoc, Ring.inverse_mul_cancel _
    (IsUnit.natCast_factorial_of_algebra ℚ n), mul_one, zero_mul] at hem
  apply hAC
  simpa only [map_zero] using hem

/-- 有理代数への単射の下での、既存一元分冪代数の実基底。 -/
def rankOneDPBasis (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) :
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  Module.Basis.mk (rankOneDP_linearIndependent C hAC) (by rw [rankOneDP_span_eq_top])

/-- 構成した基底の値は元の標準分冪生成元そのもの。 -/
theorem rankOneDPBasis_apply (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) (n : ℕ) :
    rankOneDPBasis C hAC n = DividedPowerAlgebra.dp A n (1 : A) :=
  Module.Basis.mk_apply _ _ _

end SerrePositivity.BhattScholze

end RankOneDPBasis

/-! ## 任意係数環上の既存一元分冪代数の実基底

整数係数の基底を無条件の実基底変更同型で移す。係数のpねじれを許す。
-/

@[expose] public noncomputable section RankOneDPAnyBasis

namespace SerrePositivity.BhattScholze

/-- 任意の可換環上の既存一元分冪代数の、標準分冪による実基底。 -/
def rankOneDPAnyBasis (A : Type u) [CommRing A] :
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  (((rankOneDPBasis (A := ℤ) ℚ Int.cast_injective).baseChange A).map
    (rankOneDPBaseChangeUniversalEquiv (A := ℤ) (B := A)).toLinearEquiv)

/-- 任意係数で構成した実基底の値は、元の標準生成元γ_n(1)。 -/
theorem rankOneDPAnyBasis_apply (A : Type u) [CommRing A] (n : ℕ) :
    rankOneDPAnyBasis A n = DividedPowerAlgebra.dp A n (1 : A) := by
  rw [rankOneDPAnyBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rankOneDPBasis_apply]
  exact rankOneDPBaseChangeMap_dp n

/-- 任意の可換係数環で、既存一元分冪代数は自由。 -/
theorem rankOneDPAny_moduleFree (A : Type u) [CommRing A] :
    Module.Free A (DividedPowerAlgebra A A) :=
  Module.Free.of_basis (rankOneDPAnyBasis A)

/-- 係数環の正則元は、任意係数の既存一元分冪代数上でも正則。 -/
theorem rankOneDPAny_isSMulRegular {A : Type u} [CommRing A] (r : A)
    (hr : IsSMulRegular A r) :
    IsSMulRegular (DividedPowerAlgebra A A) (algebraMap A (DividedPowerAlgebra A A) r) := by
  let : Module.Free A (DividedPowerAlgebra A A) := rankOneDPAny_moduleFree A
  exact hr.of_flat

end SerrePositivity.BhattScholze

end RankOneDPAnyBasis

/-! ## p局所・p正則な環上の一元分冪代数の基底とp正則性

任意係数の標準基底を使い、従来の仮定を持つ公開署名を互換入口として保つ。
-/

@[expose] public noncomputable section RankOneDPPrimeBasis

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

set_option linter.unusedVariables false in
/-- 任意係数の標準分冪基底を返す、p局所・p正則係数の互換入口。 -/
def rankOneDPPrimeBasis {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  rankOneDPAnyBasis A

/-- p局所係数での実基底の各元は、元のγ_n(1)そのもの。 -/
theorem rankOneDPPrimeBasis_apply (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (n : ℕ) :
    rankOneDPPrimeBasis hA hpA n = DividedPowerAlgebra.dp A n (1 : A) :=
  rankOneDPAnyBasis_apply A n

/-- 既存一元分冪代数の、p局所・p正則な元の環上の自由性。 -/
theorem rankOneDPPrime_moduleFree (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Module.Free A (DividedPowerAlgebra A A) :=
  Module.Free.of_basis (rankOneDPPrimeBasis hA hpA)

/-- p局所・p正則な環の既存一元分冪代数もp正則。 -/
theorem rankOneDPPrime_p_mul_injective (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Function.Injective (fun b : DividedPowerAlgebra A A ↦ (p : DividedPowerAlgebra A A) * b) := by
  let : Module.Free A (DividedPowerAlgebra A A) := rankOneDPPrime_moduleFree hA hpA
  have hr : IsRegular (p : A) := ⟨hpA, by
    intro x z h
    apply hpA
    simpa only [mul_comm] using h⟩
  have h := Module.Flat.isSMulRegular_of_isRegular (M := DividedPowerAlgebra A A) hr
  simpa only [IsSMulRegular, Algebra.smul_def, map_natCast] using h

end SerrePositivity.BhattScholze

end RankOneDPPrimeBasis

/-! ## p=0の係数環上の一元分冪基底の次数ブロック計算

零環も許し、CharPのインスタンスは要求しない。
-/

@[expose] public noncomputable section RankOneDPPrimeBlocks

namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A

/-- 一次生成元を掛けたときの全標準分冪生成元上の式。 -/
theorem rankOneDPGenerator_mul (n : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) * DividedPowerAlgebra.dp A n (1 : A) =
      (n + 1 : ℕ) * DividedPowerAlgebra.dp A (n + 1) (1 : A) := by
  simpa only [Nat.choose_one_right, Nat.add_comm, nsmul_eq_mul] using
    (DividedPowerAlgebra.dp_mul (R := A) (n := 1) (p := n) (m := (1 : A)))

/-- p=0なら、次数pk+rの基底への一次生成元の作用係数はr+1。 -/
theorem rankOneDPGenerator_mul_prime_block {p : ℕ} (hp : (p : A) = 0) (k r : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) * DividedPowerAlgebra.dp A (p * k + r) (1 : A) =
      (r + 1 : ℕ) * DividedPowerAlgebra.dp A (p * k + r + 1) (1 : A) := by
  rw [rankOneDPGenerator_mul]
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  simp only [Nat.cast_add, Nat.cast_mul, hpD, zero_mul, zero_add]

/-- p=0なら、次数pkの生成元へのx^rの作用はr!倍の次数pk+rの生成元。 -/
theorem rankOneDPGenerator_pow_mul_prime_block {p : ℕ} (hp : (p : A) = 0) (k r : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) ^ r * DividedPowerAlgebra.dp A (p * k) (1 : A) =
      (r.factorial : DA) * DividedPowerAlgebra.dp A (p * k + r) (1 : A) := by
  induction r with
  | zero => simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, Nat.add_zero]
  | succ r ih =>
      calc
        _ = (r.factorial : DA) * (DividedPowerAlgebra.dp A 1 (1 : A) *
            DividedPowerAlgebra.dp A (p * k + r) (1 : A)) := by
          rw [pow_succ', mul_assoc, ih]
          ring
        _ = (r.factorial : DA) * ((r + 1 : ℕ) *
            DividedPowerAlgebra.dp A (p * k + r + 1) (1 : A)) := by
          rw [rankOneDPGenerator_mul_prime_block hp]
        _ = _ := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          simp only [Nat.add_assoc]
          ring

/-- 正のpが係数環で零なら、一次分冪生成元のp乗は零。 -/
theorem rankOneDPGenerator_pow_eq_zero {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    DividedPowerAlgebra.dp A 1 (1 : A) ^ p = 0 := by
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos le_rfl
  have hf : (p.factorial : DA) = 0 := by
    rw [hk, Nat.cast_mul, hpD, zero_mul]
  have h := rankOneDPGenerator_pow_mul_prime_block hp 0 p
  simpa only [Nat.mul_zero, Nat.zero_add, DividedPowerAlgebra.dp_zero, mul_one, hf,
    zero_mul] using h

end SerrePositivity.BhattScholze

end RankOneDPPrimeBlocks

/-! ## p=0の係数環上の実次数ブロック基底

基底は係数環A上の基底であり、切断多項式環上の自由性はまだ主張しない。
-/

@[expose] public noncomputable section RankOneDPPrimeBlockBasis

namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]

/-- 素数pが零となる係数環では、p未満の次数の階乗が単元。零環も含む。 -/
theorem rankOneDPPrimeBlock_factorial_isUnit (hprime : p.Prime) (hp : (p : A) = 0)
    {r : ℕ} (hr : r < p) : IsUnit (r.factorial : A) := by
  have hnot : ¬p ∣ r.factorial := fun h ↦ (Nat.not_le_of_lt hr) (hprime.dvd_factorial.mp h)
  have hc : IsCoprime (p : A) (r.factorial : A) :=
    ((hprime.coprime_iff_not_dvd).mpr hnot).cast
  rw [hp] at hc
  exact isCoprime_zero_left.mp hc

/-- x^rγ_(pk)を全基底元とする、ℕ×Fin pで添字付けた実A加群基底。 -/
def rankOneDPPrimeBlockBasis (hprime : p.Prime) (hp : (p : A) = 0) :
    Module.Basis (ℕ × Fin p) A (DividedPowerAlgebra A A) := by
  letI : NeZero p := ⟨hprime.ne_zero⟩
  exact ((rankOneDPAnyBasis A).reindex (Nat.divModEquiv p)).isUnitSMul
    (w := fun z : ℕ × Fin p ↦ ((z.2 : ℕ).factorial : A))
    (fun z ↦ rankOneDPPrimeBlock_factorial_isUnit hprime hp z.2.is_lt)

/-- 実ブロック基底の各元は、指定されたx^rγ_(pk)に一致する。 -/
theorem rankOneDPPrimeBlockBasis_apply (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) :
    rankOneDPPrimeBlockBasis hprime hp (k, r) =
      DividedPowerAlgebra.dp A 1 (1 : A) ^ (r : ℕ) *
        DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  dsimp only [rankOneDPPrimeBlockBasis]
  rw [Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply, rankOneDPAnyBasis_apply]
  change (r.val.factorial : A) • DividedPowerAlgebra.dp A (k * p + r.val) (1 : A) = _
  rw [Nat.mul_comm k p]
  simpa only [Algebra.smul_def, map_natCast] using
    (rankOneDPGenerator_pow_mul_prime_block hp k r.val).symm

/-- 一次生成元は、各ブロックの内部で次の基底元へ進める。 -/
theorem rankOneDPPrimeBlockBasis_mul (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) (hr : r.val + 1 < p) :
    DividedPowerAlgebra.dp A 1 (1 : A) * rankOneDPPrimeBlockBasis hprime hp (k, r) =
      rankOneDPPrimeBlockBasis hprime hp (k, ⟨r.val + 1, hr⟩) := by
  rw [rankOneDPPrimeBlockBasis_apply, rankOneDPPrimeBlockBasis_apply, pow_succ', mul_assoc]

/-- 一次生成元は、各ブロックの最後の基底元を零へ送る。 -/
theorem rankOneDPPrimeBlockBasis_last_mul (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) (hr : r.val + 1 = p) :
    DividedPowerAlgebra.dp A 1 (1 : A) * rankOneDPPrimeBlockBasis hprime hp (k, r) = 0 := by
  rw [rankOneDPPrimeBlockBasis_apply, ← mul_assoc, ← pow_succ', hr,
    rankOneDPGenerator_pow_eq_zero hprime.pos hp, zero_mul]

end SerrePositivity.BhattScholze

end RankOneDPPrimeBlockBasis

/-! ## 実切断多項式環の作用と標準冪基底

既存AdjoinRootをそのまま使い、根を一次分冪生成元へ送る。
-/

@[expose] public noncomputable section RankOneDPTruncatedAction

namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A
local notation "T₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 根を一次分冪生成元へ送る、実切断多項式環からのA代数射。 -/
def rankOneDPTruncatedMap (hpos : 0 < p) (hp : (p : A) = 0) : T₀ →ₐ[A] DA :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p) (Algebra.ofId A DA)
    (DividedPowerAlgebra.dp A 1 (1 : A)) (by
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact rankOneDPGenerator_pow_eq_zero hpos hp)

/-- 実作用射は、切断多項式環の根を指定された一次生成元へ送る。 -/
theorem rankOneDPTruncatedMap_root (hpos : 0 < p) (hp : (p : A) = 0) :
    rankOneDPTruncatedMap hpos hp (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p)) =
      DividedPowerAlgebra.dp A 1 (1 : A) := by
  exact AdjoinRoot.lift_root (i := algebraMap A DA) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    exact rankOneDPGenerator_pow_eq_zero hpos hp)

/-- 上の実射による、切断多項式環の具体的スカラー作用。 -/
abbrev rankOneDPTruncatedAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra T₀ DA :=
  (rankOneDPTruncatedMap hpos hp).toRingHom.toAlgebra

/-- 指定した切断多項式作用と元の係数環の作用は、実スカラー塔をなす。 -/
theorem rankOneDPTruncated_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hpos hp
    IsScalarTower A T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (fun a ↦ (rankOneDPTruncatedMap hpos hp).commutes a |>.symm)

/-- 非零係数環での、実切断多項式環のFin pで添字付けた標準冪基底。 -/
def rankOneDPTruncatedBasis (p : ℕ) (A : Type u) [CommRing A] [Nontrivial A] :
    Module.Basis (Fin p) A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
  ((AdjoinRoot.powerBasis' (Polynomial.monic_X_pow p)).basis).reindex
    (finCongr (Polynomial.natDegree_X_pow (R := A) p))

/-- 標準冪基底の各元は、切断多項式環の実根のr乗。 -/
theorem rankOneDPTruncatedBasis_apply [Nontrivial A] (r : Fin p) :
    rankOneDPTruncatedBasis p A r =
      AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ^ (r : ℕ) := by
  rw [rankOneDPTruncatedBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- 標準冪基底の作用像は、一次分冪生成元の対応する冪。 -/
theorem rankOneDPTruncatedMap_basis [Nontrivial A] (hpos : 0 < p) (hp : (p : A) = 0)
    (r : Fin p) :
    rankOneDPTruncatedMap hpos hp (rankOneDPTruncatedBasis p A r) =
      DividedPowerAlgebra.dp A 1 (1 : A) ^ (r : ℕ) := by
  rw [rankOneDPTruncatedBasis_apply, map_pow, rankOneDPTruncatedMap_root]

end SerrePositivity.BhattScholze

end RankOneDPTruncatedAction

/-! ## 実切断多項式環上の一元分冪代数の自由性

零係数環を含む。指定した実作用について自由性と忠実平坦性を証明する。
-/

@[expose] public noncomputable section RankOneDPTruncatedFree

namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "DA" => DividedPowerAlgebra A A
local notation "T₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- γ_(pk)に沿う、指定された切断多項式作用についての実線形結合写像。 -/
def rankOneDPTruncatedCombination :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    (ℕ →₀ T₀) →ₗ[T₀] DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Finsupp.linearCombination T₀ (fun k : ℕ ↦ DividedPowerAlgebra.dp A (p * k) (1 : A))

/-- 実線形結合写像の一項係数族上の式。 -/
theorem rankOneDPTruncatedCombination_single (k : ℕ) (c : T₀) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedCombination hprime hp (Finsupp.single k c) =
      c • DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Finsupp.linearCombination_single T₀ c k

/-- 実線形結合写像は、零係数環を含めて全単射。 -/
theorem rankOneDPTruncatedCombination_bijective :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Function.Bijective (rankOneDPTruncatedCombination hprime hp) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower A T₀ DA := rankOneDPTruncated_isScalarTower hprime.pos hp
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    let : Subsingleton T₀ := Module.subsingleton A T₀
    let : Subsingleton DA := Module.subsingleton A DA
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun z ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · let := hA
    let bC := rankOneDPTruncatedBasis p A
    let bF : Module.Basis (ℕ × Fin p) A (ℕ →₀ T₀) :=
      (Finsupp.basis (fun _ : ℕ ↦ bC)).reindex (Equiv.sigmaEquivProd ℕ (Fin p))
    let bD := rankOneDPPrimeBlockBasis hprime hp
    let e := bF.equiv bD (Equiv.refl (ℕ × Fin p))
    let L := rankOneDPTruncatedCombination hprime hp
    have he : L.restrictScalars A = e.toLinearMap := by
      apply bF.ext
      rintro ⟨k, r⟩
      change L (bF (k, r)) = e (bF (k, r))
      rw [Module.Basis.equiv_apply]
      change L (((Finsupp.basis (fun _ : ℕ ↦ bC)).reindex
        (Equiv.sigmaEquivProd ℕ (Fin p))) (k, r)) = bD (k, r)
      rw [Module.Basis.reindex_apply]
      simp only [Finsupp.coe_basis]
      change L (Finsupp.single k (bC r)) = bD (k, r)
      rw [rankOneDPTruncatedCombination_single]
      change rankOneDPTruncatedMap hprime.pos hp (rankOneDPTruncatedBasis p A r) *
        DividedPowerAlgebra.dp A (p * k) (1 : A) = rankOneDPPrimeBlockBasis hprime hp (k, r)
      rw [rankOneDPTruncatedMap_basis, rankOneDPPrimeBlockBasis_apply]
    change Function.Bijective (L.restrictScalars A)
    rw [he]
    exact e.bijective

/-- 指定作用に関する、実切断多項式環上の標準自由加群との線形同値。 -/
def rankOneDPTruncatedEquiv :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    (ℕ →₀ T₀) ≃ₗ[T₀] DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact LinearEquiv.ofBijective (rankOneDPTruncatedCombination hprime hp)
    (rankOneDPTruncatedCombination_bijective hprime hp)

/-- 実線形同値の一項係数族上の具体式。 -/
theorem rankOneDPTruncatedEquiv_single (k : ℕ) (c : T₀) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedEquiv hprime hp (Finsupp.single k c) =
      c • DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncatedCombination_single hprime hp k c

/-- 実切断多項式環上でγ_(pk)を基底元とする実基底。 -/
def rankOneDPTruncatedBlockBasis :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Basis ℕ T₀ DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact (Finsupp.basisSingleOne : Module.Basis ℕ T₀ (ℕ →₀ T₀)).map
    (rankOneDPTruncatedEquiv hprime hp)

/-- 実切断多項式環上の各基底元は、指定された分冪生成元γ_(pk)。 -/
theorem rankOneDPTruncatedBlockBasis_apply (k : ℕ) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedBlockBasis hprime hp k = DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  rw [rankOneDPTruncatedBlockBasis, Module.Basis.map_apply]
  simp only [Finsupp.coe_basisSingleOne]
  rw [rankOneDPTruncatedEquiv_single, one_smul]

/-- 一元分冪代数は、指定した実切断多項式作用について自由。零環も含む。 -/
theorem rankOneDPTruncated_moduleFree :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Free T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Module.Free.of_basis (rankOneDPTruncatedBlockBasis hprime hp)

/-- 一元分冪代数は、指定した実切断多項式作用について平坦。 -/
theorem rankOneDPTruncated_moduleFlat :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Flat T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : Module.Free T₀ DA := rankOneDPTruncated_moduleFree hprime hp
  infer_instance

/-- 一元分冪代数は、指定した実切断多項式作用について忠実平坦。零環も含む。 -/
theorem rankOneDPTruncated_moduleFaithfullyFlat :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.FaithfullyFlat T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Module.FaithfullyFlat.of_linearEquiv T₀ (ℕ →₀ T₀)
    (rankOneDPTruncatedEquiv hprime hp).symm

end SerrePositivity.BhattScholze

end RankOneDPTruncatedFree

/-! ## 多項式作用と切断多項式作用の実因子化

テンソルとTorで使う多項式環の作用を指定した実環射で明示する。
-/

@[expose] public noncomputable section RankOneDPPolynomialAction

namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A

/-- 多項式変数を一次分冪生成元へ送る実A代数射。 -/
def rankOneDPPolynomialMap (A : Type u) [CommRing A] : Polynomial A →ₐ[A] DividedPowerAlgebra A A :=
  Polynomial.aeval (DividedPowerAlgebra.dp A 1 (1 : A))

/-- 指定された実多項式射の変数上の式。 -/
theorem rankOneDPPolynomialMap_X :
    rankOneDPPolynomialMap A Polynomial.X = DividedPowerAlgebra.dp A 1 (1 : A) :=
  Polynomial.aeval_X _

/-- 指定された実多項式射の係数上の式。 -/
theorem rankOneDPPolynomialMap_C (a : A) :
    rankOneDPPolynomialMap A (Polynomial.C a) = algebraMap A DA a :=
  Polynomial.aeval_C _ _

/-- 指定された多項式射による具体的スカラー作用。 -/
abbrev rankOneDPPolynomialAlgebra (A : Type u) [CommRing A] :
    Algebra (Polynomial A) (DividedPowerAlgebra A A) :=
  (rankOneDPPolynomialMap A).toRingHom.toAlgebra

/-- 指定された多項式作用と元の係数作用の実スカラー塔。 -/
theorem rankOneDPPolynomial_isScalarTower :
    letI : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
    IsScalarTower A (Polynomial A) DA := by
  let : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
  exact IsScalarTower.of_algebraMap_eq (fun a ↦ (rankOneDPPolynomialMap A).commutes a |>.symm)

/-- 実商写像mkによる、切断多項式環の具体的な多項式環上の代数構造。 -/
abbrev rankOneDPPolynomialQuotientAlgebra (p : ℕ) (A : Type u) [CommRing A] :
    Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
  (AdjoinRoot.mk ((Polynomial.X : Polynomial A) ^ p)).toAlgebra

/-- 実商写像による切断多項式作用も元の係数作用と可換。 -/
theorem rankOneDPPolynomialQuotient_isScalarTower (p : ℕ) :
    letI : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
      rankOneDPPolynomialQuotientAlgebra p A
    IsScalarTower A (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) := by
  let : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
    rankOneDPPolynomialQuotientAlgebra p A
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- 元の多項式作用は、実商写像と切断多項式作用の合成そのもの。 -/
theorem rankOneDPPolynomial_truncated_comp {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hpos hp).toRingHom.comp
        (AdjoinRoot.mk ((Polynomial.X : Polynomial A) ^ p)) =
      (rankOneDPPolynomialMap A).toRingHom := by
  apply RingHom.ext
  intro f
  exact AdjoinRoot.lift_mk (i := algebraMap A DA) (a := DividedPowerAlgebra.dp A 1 (1 : A))
    (by
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact rankOneDPGenerator_pow_eq_zero hpos hp) f

/-- 多項式作用、実切断多項式作用、分冪代数の間の実スカラー塔。 -/
theorem rankOneDPPolynomial_truncated_isScalarTower {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
    letI : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
      rankOneDPPolynomialQuotientAlgebra p A
    letI : Algebra (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA :=
      rankOneDPTruncatedAlgebra hpos hp
    IsScalarTower (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA := by
  let : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
  let : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
    rankOneDPPolynomialQuotientAlgebra p A
  let : Algebra (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA :=
    rankOneDPTruncatedAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq
    (fun f ↦ (RingHom.congr_fun (rankOneDPPolynomial_truncated_comp hpos hp) f).symm)

end SerrePositivity.BhattScholze

end RankOneDPPolynomialAction

/-! ## 通常一元分冪添加環への実テンソル基底変更

Bへの多項式作用はAlgebra (Polynomial A) Bとして指定する。
-/

@[expose] public noncomputable section RankOneDPEnvelopeBaseChange

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A

/-- 指定された多項式作用に沿って実切断多項式環を基底変更した環。 -/
abbrev RankOneDPBaseChangedTruncation (p : ℕ) (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (Polynomial A) B] :=
  AdjoinRoot ((Polynomial.X : Polynomial A) ^ p) ⊗[Polynomial A] B

/-- 指定された多項式作用に沿う、通常の実一元分冪添加テンソル環。 -/
abbrev RankOneDPBaseChangedEnvelope (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (Polynomial A) B] :=
  DividedPowerAlgebra A A ⊗[Polynomial A] B

local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実切断多項式作用の基底変更で与えられる、UからDへの実比較射。 -/
def rankOneDPEnvelopeBaseChangeMap (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    U₀ →ₐ[C₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact Algebra.TensorProduct.map (Algebra.ofId C₀ DA) (AlgHom.id P₀ B)

/-- 実比較射の全純テンソル上の具体式。 -/
theorem rankOneDPEnvelopeBaseChangeMap_tmul (hpos : 0 < p) (hp : (p : A) = 0) (c : C₀) (b : B) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    rankOneDPEnvelopeBaseChangeMap hpos hp (c ⊗ₜ[P₀] b) =
      rankOneDPTruncatedMap hpos hp c ⊗ₜ[P₀] b := by
  rfl

/-- 通常分冪添加環は、切断多項式環上の自由加群をUへ基底変更した実環に同型。 -/
def rankOneDPEnvelopeTensorEquiv (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    U₀ ⊗[C₀] DA ≃ₐ[C₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (Algebra.TensorProduct.comm C₀ U₀ DA).trans
    (Algebra.TensorProduct.cancelBaseChange P₀ C₀ C₀ DA B)

/-- 実基底変更同型の全生成純テンソル上の式。 -/
theorem rankOneDPEnvelopeTensorEquiv_tmul (hpos : 0 < p) (hp : (p : A) = 0)
    (c : C₀) (b : B) (t : DA) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    rankOneDPEnvelopeTensorEquiv hpos hp ((c ⊗ₜ[P₀] b) ⊗ₜ[C₀] t) =
      (rankOneDPTruncatedMap hpos hp c * t) ⊗ₜ[P₀] b := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  rw [rankOneDPEnvelopeTensorEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  rfl

/-- 実同型はUの標準射を、指定された実比較射へ送る。 -/
theorem rankOneDPEnvelopeTensorEquiv_comp_includeLeft (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    (rankOneDPEnvelopeTensorEquiv hpos hp).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (R := C₀) (A := U₀) (B := DA)) =
      rankOneDPEnvelopeBaseChangeMap hpos hp := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  apply Algebra.TensorProduct.ext'
  intro c b
  change rankOneDPEnvelopeTensorEquiv hpos hp ((c ⊗ₜ[P₀] b) ⊗ₜ[C₀] (1 : DA)) = _
  rw [rankOneDPEnvelopeTensorEquiv_tmul, rankOneDPEnvelopeBaseChangeMap_tmul, mul_one]

/-- 実比較射U→Dによる具体的U代数構造。 -/
abbrev rankOneDPEnvelopeBaseChangedAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra U₀ D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (rankOneDPEnvelopeBaseChangeMap (B := B) hpos hp).toRingHom.toAlgebra

/-- 実比較射によるU作用を保つ、実U代数同型。 -/
def rankOneDPEnvelopeBaseChangeEquiv (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
    U₀ ⊗[C₀] DA ≃ₐ[U₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
  exact
    { __ := (rankOneDPEnvelopeTensorEquiv hpos hp).toRingEquiv
      commutes' := fun u ↦
        DFunLike.congr_fun (rankOneDPEnvelopeTensorEquiv_comp_includeLeft hpos hp) u }

end SerrePositivity.BhattScholze

end RankOneDPEnvelopeBaseChange

/-! ## 基底変更した実切断多項式環とB/(y^p)の同定 -/

@[expose] public noncomputable section RankOneDPTruncationQuotient

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialQuotientAlgebra
variable (p : ℕ) {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "y₀" => algebraMap P₀ B Polynomial.X
local notation "J₀" => Ideal.span {y₀ ^ p}
local notation "U₀" => RankOneDPBaseChangedTruncation p A B

/-- X^pの主イデアルの像は、指定した変数の像のp乗の主イデアル。 -/
theorem rankOneDPTruncationRelationIdeal_map :
    (Ideal.span {(Polynomial.X : P₀) ^ p}).map (algebraMap P₀ B) = J₀ := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

/-- 基底変更した実切断多項式環と、指定されたBの実商との環同型。 -/
def rankOneDPTruncationQuotientEquiv : B ⧸ J₀ ≃+* U₀ := by
  let I : Ideal P₀ := Ideal.span {(Polynomial.X : P₀) ^ p}
  have hI : I.map (algebraMap P₀ B) = J₀ := rankOneDPTruncationRelationIdeal_map p
  exact (Ideal.quotEquivOfEq hI.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm P₀ B C₀).toRingEquiv)

/-- 実商の任意の代表元は、対応する標準純テンソルへ送られる。 -/
theorem rankOneDPTruncationQuotientEquiv_mk (b : B) :
    rankOneDPTruncationQuotientEquiv (A := A) p (Ideal.Quotient.mk J₀ b) =
      (1 : C₀) ⊗ₜ[P₀] b := by
  rfl

/-- 指定された変数の商像は、実切断多項式環の根の基底変更像へ送られる。 -/
theorem rankOneDPTruncationQuotientEquiv_variable :
    rankOneDPTruncationQuotientEquiv (A := A) (B := B) p (Ideal.Quotient.mk J₀ y₀) =
      AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[P₀] (1 : B) := by
  rw [rankOneDPTruncationQuotientEquiv_mk]
  have h := TensorProduct.smul_tmul (R := P₀) (Polynomial.X : P₀) (1 : C₀) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  exact h.symm

end SerrePositivity.BhattScholze

end RankOneDPTruncationQuotient

/-! ## 基底変更後の通常分冪添加環の自由性と忠実平坦性 -/

@[expose] public noncomputable section RankOneDPEnvelopeFree

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A
local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実比較射U→Dの作用に関する、基底変更後の実分冪基底。 -/
def rankOneDPEnvelopeBasis :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Basis ℕ U₀ D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  exact ((rankOneDPTruncatedBlockBasis hprime hp).baseChange U₀).map
    (rankOneDPEnvelopeBaseChangeEquiv hprime.pos hp).toLinearEquiv

/-- 実U基底の各元は指定されたγ_(pk)⊗1。 -/
theorem rankOneDPEnvelopeBasis_apply (k : ℕ) :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    rankOneDPEnvelopeBasis hprime hp k =
      DividedPowerAlgebra.dp A (p * k) (1 : A) ⊗ₜ[P₀] (1 : B) := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  rw [rankOneDPEnvelopeBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rankOneDPTruncatedBlockBasis_apply]
  change rankOneDPEnvelopeTensorEquiv hprime.pos hp
    ((1 : U₀) ⊗ₜ[C₀] DividedPowerAlgebra.dp A (p * k) (1 : A)) = _
  rw [show (1 : U₀) = (1 : C₀) ⊗ₜ[P₀] (1 : B) from Algebra.TensorProduct.one_def,
    rankOneDPEnvelopeTensorEquiv_tmul, map_one, one_mul]

/-- 通常分冪添加環は指定されたU作用について自由。零環も含む。 -/
theorem rankOneDPEnvelope_moduleFree :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Free U₀ D₀ := by
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  exact Module.Free.of_basis (rankOneDPEnvelopeBasis hprime hp)

/-- 通常分冪添加環は指定されたU作用について平坦。 -/
theorem rankOneDPEnvelope_moduleFlat :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Flat U₀ D₀ := by
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Module.Free U₀ D₀ := rankOneDPEnvelope_moduleFree hprime hp
  infer_instance

/-- 通常分冪添加環は指定されたU作用について忠実平坦。零環も含む。 -/
theorem rankOneDPEnvelope_moduleFaithfullyFlat :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.FaithfullyFlat U₀ D₀ := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Module.FaithfullyFlat C₀ DA := rankOneDPTruncated_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.of_linearEquiv U₀ (U₀ ⊗[C₀] DA)
    (rankOneDPEnvelopeBaseChangeEquiv hprime.pos hp).symm.toLinearEquiv

end SerrePositivity.BhattScholze

end RankOneDPEnvelopeFree

/-! ## 実商B/(y^p)から通常分冪添加環への自由・忠実平坦な実射 -/

@[expose] public noncomputable section RankOneDPQuotientToEnvelope

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A
local notation "Q₀" => B ⧸ Ideal.span {(algebraMap P₀ B Polynomial.X) ^ p}
local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実商からの、全代表元bを1⊗bへ送る実環射。 -/
def rankOneDPQuotientToEnvelope (hpos : 0 < p) (hp : (p : A) = 0) : Q₀ →+* D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (rankOneDPEnvelopeBaseChangeMap hpos hp).toRingHom.comp
    (rankOneDPTruncationQuotientEquiv (A := A) (B := B) p).toRingHom

/-- 実商からの環射の、全代表元上の具体式。 -/
theorem rankOneDPQuotientToEnvelope_mk (hpos : 0 < p) (hp : (p : A) = 0) (b : B) :
    rankOneDPQuotientToEnvelope hpos hp (Ideal.Quotient.mk _ b) = (1 : DA) ⊗ₜ[P₀] b := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  change rankOneDPEnvelopeBaseChangeMap hpos hp
    (rankOneDPTruncationQuotientEquiv (A := A) p (Ideal.Quotient.mk _ b)) = _
  rw [rankOneDPTruncationQuotientEquiv_mk, rankOneDPEnvelopeBaseChangeMap_tmul, map_one]

/-- 実商同型による、Uの具体的な商環上のスカラー作用。 -/
abbrev rankOneDPTruncationQuotientAlgebra : Algebra Q₀ U₀ :=
  (rankOneDPTruncationQuotientEquiv (A := A) (B := B) p).toRingHom.toAlgebra

/-- 実商から分冪添加環への指定した射による具体的代数構造。 -/
abbrev rankOneDPQuotientToEnvelopeAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra Q₀ D₀ :=
  (rankOneDPQuotientToEnvelope (B := B) hpos hp).toAlgebra

/-- 実商からUを経由する指定されたスカラー塔。 -/
theorem rankOneDPQuotientToEnvelope_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
    IsScalarTower Q₀ U₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- 指定された実射について、通常分冪添加環はB/(y^p)上自由。 -/
theorem rankOneDPQuotientToEnvelope_moduleFree (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.Free Q₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower Q₀ U₀ D₀ := rankOneDPQuotientToEnvelope_isScalarTower hprime.pos hp
  let e : Q₀ ≃ₐ[Q₀] U₀ :=
    { __ := rankOneDPTruncationQuotientEquiv (A := A) (B := B) p
      commutes' := fun _ ↦ rfl }
  let b : Module.Basis Unit Q₀ U₀ := (Module.Basis.singleton Unit Q₀).map e.toLinearEquiv
  exact Module.Free.of_basis (b.smulTower (rankOneDPEnvelopeBasis hprime hp))

/-- 指定された実射について、通常分冪添加環はB/(y^p)上平坦。 -/
theorem rankOneDPQuotientToEnvelope_moduleFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.Flat Q₀ D₀ := by
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Module.Free Q₀ D₀ := rankOneDPQuotientToEnvelope_moduleFree hprime hp
  infer_instance

/-- 指定された実射について、通常分冪添加環はB/(y^p)上忠実平坦。零環も含む。 -/
theorem rankOneDPQuotientToEnvelope_moduleFaithfullyFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.FaithfullyFlat Q₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower Q₀ U₀ D₀ := rankOneDPQuotientToEnvelope_isScalarTower hprime.pos hp
  let e : Q₀ ≃ₐ[Q₀] U₀ :=
    { __ := rankOneDPTruncationQuotientEquiv (A := A) (B := B) p
      commutes' := fun _ ↦ rfl }
  let : Module.FaithfullyFlat Q₀ U₀ :=
    Module.FaithfullyFlat.of_linearEquiv Q₀ Q₀ e.symm.toLinearEquiv
  let : Module.FaithfullyFlat U₀ D₀ := rankOneDPEnvelope_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.trans Q₀ U₀ D₀

end SerrePositivity.BhattScholze

end RankOneDPQuotientToEnvelope

/-! ## 通常分冪添加環の実係数射と係数環上の平坦性 -/

@[expose] public noncomputable section RankOneDPEnvelopeCoefficientFlat

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "DA" => DividedPowerAlgebra A A
local notation "Q₀" => B ⧸ Ideal.span {(algebraMap P₀ B Polynomial.X) ^ p}
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 指定された多項式作用から実商へ誘導される実係数射。 -/
def rankOneDPPowerQuotientCoefficientMap : A →+* Q₀ :=
  (Ideal.Quotient.mk _).comp ((algebraMap P₀ B).comp Polynomial.C)

/-- 分冪添加環の左成分を通じる実係数射。 -/
def rankOneDPEnvelopeCoefficientMap : A →+* D₀ :=
  (Algebra.TensorProduct.includeLeft (R := P₀) (S := P₀) (A := DA) (B := B)).toRingHom.comp
    (algebraMap A DA)

/-- 実商への係数射による具体的A代数構造。 -/
abbrev rankOneDPPowerQuotientCoefficientAlgebra : Algebra A Q₀ :=
  (rankOneDPPowerQuotientCoefficientMap (p := p) (A := A) (B := B)).toAlgebra

/-- 分冪添加環への係数射による具体的A代数構造。 -/
abbrev rankOneDPEnvelopeCoefficientAlgebra : Algebra A D₀ :=
  (rankOneDPEnvelopeCoefficientMap (A := A) (B := B)).toAlgebra

/-- 実商から分冪添加環への射は、指定した両実係数射と可換。 -/
theorem rankOneDPQuotientToEnvelope_comp_coefficient (hpos : 0 < p) (hp : (p : A) = 0) :
    (rankOneDPQuotientToEnvelope (B := B) hpos hp).comp
        rankOneDPPowerQuotientCoefficientMap =
      rankOneDPEnvelopeCoefficientMap := by
  apply RingHom.ext
  intro a
  change rankOneDPQuotientToEnvelope hpos hp
    (Ideal.Quotient.mk _ (algebraMap P₀ B (Polynomial.C a))) =
      (algebraMap A DA a) ⊗ₜ[P₀] (1 : B)
  rw [rankOneDPQuotientToEnvelope_mk]
  have h := TensorProduct.smul_tmul (R := P₀) (Polynomial.C a : P₀) (1 : DA) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  change (rankOneDPPolynomialMap A (Polynomial.C a)) ⊗ₜ[P₀] (1 : B) =
    (1 : DA) ⊗ₜ[P₀] algebraMap P₀ B (Polynomial.C a) at h
  rw [rankOneDPPolynomialMap_C] at h
  exact h.symm

/-- 実商の平坦性を分冪添加環へ移すための、実係数スカラー塔。 -/
theorem rankOneDPEnvelopeCoefficient_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
    IsScalarTower A Q₀ D₀ := by
  let : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (R := A) (S := Q₀) (A := D₀)
    (fun a ↦ (RingHom.congr_fun (rankOneDPQuotientToEnvelope_comp_coefficient hpos hp) a).symm)

/-- 実商B/(y^p)が係数環上平坦なら、通常分冪添加環も指定した係数作用について平坦。 -/
theorem rankOneDPEnvelope_flat_of_quotient_flat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
    Module.Flat A Q₀ → Module.Flat A D₀ := by
  let : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower A Q₀ D₀ := rankOneDPEnvelopeCoefficient_isScalarTower hprime.pos hp
  intro hQ
  let := hQ
  let : Module.Flat Q₀ D₀ := rankOneDPQuotientToEnvelope_moduleFlat hprime hp
  exact Module.Flat.trans A Q₀ D₀

end SerrePositivity.BhattScholze

end RankOneDPEnvelopeCoefficientFlat

/-! ## 具体的A代数Bと元yへの通常分冪添加の評価入口

元の係数作用と商の自然な作用を保ったまま、通常の平坦性を移す。
-/

@[expose] public noncomputable section RankOneDPEvaluatedEnvelope

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 元yへの既存aevalが指定する、Bへの具体的多項式作用。 -/
abbrev rankOneDPEvaluationAlgebra (y : B) : Algebra (Polynomial A) B :=
  (Polynomial.aeval y).toRingHom.toAlgebra

/-- 元の係数作用とyへの評価作用は実スカラー塔をなす。 -/
theorem rankOneDPEvaluation_isScalarTower (y : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    IsScalarTower A (Polynomial A) B := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  exact IsScalarTower.of_algebraMap_eq (R := A) (S := Polynomial A) (A := B)
    (fun a ↦ (Polynomial.aeval y).commutes a |>.symm)

/-- Bの指定元yへの実評価作用で作った通常分冪添加テンソル環。 -/
abbrev RankOneDPEvaluatedEnvelope (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (y : B) :=
  letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  RankOneDPBaseChangedEnvelope A B

/-- 評価した多項式変数のp乗の商は、指定された元yのp乗の商と同じ実イデアルで定義される。 -/
theorem rankOneDPEvaluatedRelationIdeal (p : ℕ) (y : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    Ideal.span {y ^ p} = Ideal.span {(algebraMap (Polynomial A) B Polynomial.X) ^ p} := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  change Ideal.span {y ^ p} = Ideal.span {(Polynomial.aeval y Polynomial.X) ^ p}
  rw [Polynomial.aeval_X]

variable {p : ℕ}

/-- 元yの実商から、評価した通常分冪添加環への具体的環射。 -/
def rankOneDPEvaluatedQuotientMap (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    B ⧸ Ideal.span {y ^ p} →+* RankOneDPEvaluatedEnvelope A B y := by
  letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  exact (rankOneDPQuotientToEnvelope (B := B) hpos hp).comp
    (Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := A) p y)).toRingHom

/-- 評価した実環射は、すべての商代表元bを1⊗bへ送る。 -/
theorem rankOneDPEvaluatedQuotientMap_mk (hpos : 0 < p) (hp : (p : A) = 0) (y b : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
      (1 : DividedPowerAlgebra A A) ⊗ₜ[Polynomial A] b := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  change rankOneDPQuotientToEnvelope hpos hp (Ideal.Quotient.mk _ b) = _
  exact rankOneDPQuotientToEnvelope_mk hpos hp b

/-- 元yの実商からの指定された環射による具体的代数構造。 -/
abbrev rankOneDPEvaluatedQuotientAlgebra (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
  (rankOneDPEvaluatedQuotientMap hpos hp y).toAlgebra

/-- 元yの実商からの指定された環射は忠実平坦。零環も含む。 -/
theorem rankOneDPEvaluatedQuotient_moduleFaithfullyFlat
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B) :
    letI : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
      rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
    Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let Q := B ⧸ Ideal.span {y ^ p}
  let Q' := B ⧸ Ideal.span {(algebraMap (Polynomial A) B Polynomial.X) ^ p}
  let D := RankOneDPEvaluatedEnvelope A B y
  let eQ : Q ≃+* Q' := Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := A) p y)
  let : Algebra Q Q' := eQ.toRingHom.toAlgebra
  let : Algebra Q' D := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Algebra Q D := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower Q Q' D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let e : Q ≃ₐ[Q] Q' := { __ := eQ, commutes' := fun _ ↦ rfl }
  let : Module.FaithfullyFlat Q Q' := Module.FaithfullyFlat.of_linearEquiv Q Q e.symm.toLinearEquiv
  let : Module.FaithfullyFlat Q' D := rankOneDPQuotientToEnvelope_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.trans Q Q' D

/-- 元のA作用、自然な商作用、指定した分冪添加作用の実スカラー塔。 -/
theorem rankOneDPEvaluatedQuotient_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    letI : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
      rankOneDPEvaluatedQuotientAlgebra hpos hp y
    IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := A) (S := B ⧸ Ideal.span {y ^ p})
    (A := RankOneDPEvaluatedEnvelope A B y)
  intro a
  change (algebraMap A (DividedPowerAlgebra A A) a) ⊗ₜ[Polynomial A] (1 : B) =
    rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ (algebraMap A B a))
  rw [rankOneDPEvaluatedQuotientMap_mk]
  have h := TensorProduct.smul_tmul (R := Polynomial A) (Polynomial.C a : Polynomial A)
    (1 : DividedPowerAlgebra A A) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  change rankOneDPPolynomialMap A (Polynomial.C a) ⊗ₜ[Polynomial A] (1 : B) =
    (1 : DividedPowerAlgebra A A) ⊗ₜ[Polynomial A] Polynomial.aeval y (Polynomial.C a) at h
  rw [rankOneDPPolynomialMap_C, Polynomial.aeval_C] at h
  exact h

/-- 自然な商A加群B/(y^p)が平坦なら、元yへ評価した通常分冪添加環もA平坦。 -/
theorem rankOneDPEvaluatedEnvelope_flat_of_quotient_flat
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hQ : Module.Flat A (B ⧸ Ideal.span {y ^ p})) :
    Module.Flat A (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotient_isScalarTower hprime.pos hp y
  let := hQ
  let : Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotient_moduleFaithfullyFlat hprime hp y
  exact Module.Flat.trans A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y)

end SerrePositivity.BhattScholze

end RankOneDPEvaluatedEnvelope

/-! ## 既存一元分冪代数の実テンソル基底変更

任意係数の実比較同型から、従来のp局所・p正則な公開署名を保つ互換入口を得る。
-/

@[expose] public noncomputable section RankOneDPBaseChange

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

variable {p : ℕ} [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
include hA hpA hB hpB

set_option linter.unusedSectionVars false in
/-- p局所・p正則係数では、実テンソル比較射は全単射。 -/
theorem rankOneDPBaseChangeMap_bijective :
    Function.Bijective (rankOneDPBaseChangeMap (A := A) (B := B)) :=
  (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).bijective

/-- p局所・p正則係数での、一元分冪代数の実基底変更同型。 -/
def rankOneDPBaseChangeEquiv :
    B ⊗[A] DividedPowerAlgebra A A ≃ₐ[B] DividedPowerAlgebra B B :=
  AlgEquiv.ofBijective rankOneDPBaseChangeMap
    (rankOneDPBaseChangeMap_bijective hA hpA hB hpB)

/-- 実基底変更同型も、全純テンソル上で構成した実比較射に一致する。 -/
theorem rankOneDPBaseChangeEquiv_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeEquiv hA hpA hB hpB (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

end SerrePositivity.BhattScholze

end RankOneDPBaseChange

/-! ## 切断多項式商の実導来係数拡大とKoszul比較

完備化は行わない。一般の評価代数を通常の商へ置換する主張は含めない。
-/

@[expose] public noncomputable section RankOneDPTruncationDerived

namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A

/-- 切断多項式を定めるX^pは、零環を含む任意係数多項式環で正則。 -/
theorem rankOneDPTruncationPolynomial_regular (p : ℕ) :
    IsSMulRegular P₀ ((Polynomial.X : P₀) ^ p) :=
  ((Polynomial.monic_X (R := A)).pow p).isRegular.left

/-- 切断多項式商への実導来係数拡大は、元の多項式環上で実Koszul coneと一致する。 -/
def rankOneDPTruncationDerivedKoszulIso (p : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    ((boundedAboveDerivedRestrictScalars
      (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj :=
  restrictedDerivedQuotientKoszulIso _ (rankOneDPTruncationPolynomial_regular p) X

variable {B : Type u} [CommRing B] [Algebra A B]

/-- 実評価作用で、多項式X^pの像は指定した元のp乗。 -/
theorem rankOneDPTruncationEvaluation_power (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    algebraMap P₀ B ((Polynomial.X : P₀) ^ p) = y ^ p := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  change Polynomial.aeval y ((Polynomial.X : P₀) ^ p) = _
  rw [map_pow, Polynomial.aeval_X]

/-- 評価加群上でのX^pの正則性は、元のB上でのy^pの正則性そのもの。 -/
theorem rankOneDPTruncationEvaluation_regular_iff (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    IsSMulRegular B ((Polynomial.X : P₀) ^ p) ↔ IsSMulRegular B (y ^ p) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  change Function.Injective (fun b : B ↦ ((Polynomial.X : P₀) ^ p) • b) ↔ _
  simp only [Algebra.smul_def, rankOneDPTruncationEvaluation_power]
  rfl

/-- 具体的評価代数Bの次数零対象に対する、切断多項式商の実導来Koszul比較。 -/
def rankOneDPTruncationEvaluationDerivedKoszulIso (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)
    ((boundedAboveDerivedRestrictScalars
      (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPTruncationDerivedKoszulIso p
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))

end SerrePositivity.BhattScholze

end RankOneDPTruncationDerived

/-! ## 一元分冪代数への実導来係数拡大の切断多項式環による因子化 -/

@[expose] public noncomputable section RankOneDPDerivedFactorization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 切断多項式環からの実分冪作用射は平坦な環射。 -/
theorem rankOneDPTruncatedRingHom_flat (hprime : p.Prime) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom.Flat := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncated_moduleFlat hprime hp

/-- 切断多項式環からの実分冪作用射は忠実平坦な環射。零環も含む。 -/
theorem rankOneDPTruncatedRingHom_faithfullyFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom.FaithfullyFlat := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncated_moduleFaithfullyFlat hprime hp

/-- P→Γへの実導来係数拡大は、実射P→C→Γに沿う二段階の拡大と一致する。 -/
def rankOneDPDerivedFactorizationIso (hpos : 0 < p) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X ≅
      (boundedAboveDerivedBaseChange (rankOneDPTruncatedMap hpos hp).toRingHom).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  apply ObjectProperty.isoMk
  refine (boundedAboveDerivedBaseChangeModelIso _ X (boundedAboveDerivedChosenModel X)) ≪≫ ?_
  have hcomp := rankOneDPPolynomial_truncated_comp hpos hp
  rw [← hcomp]
  exact DerivedCategory.Q.mapIso (baseChangeCompIso q₀
      (rankOneDPTruncatedMap hpos hp).toRingHom (boundedAboveDerivedChosenModel X).complex).symm ≪≫
    (boundedAboveDerivedBaseChangeModelIso _ _ (boundedAboveDerivedBaseChangeModel q₀ X)).symm

/-- 素数標数では、P→Γの実導来拡大をCへの実導来拡大と通常の平坦拡大に分解できる。 -/
def rankOneDPDerivedFlatFactorizationIso (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    ((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj ≅
      (flatDerivedBaseChange (rankOneDPTruncatedMap hprime.pos hp).toRingHom
        (rankOneDPTruncatedRingHom_flat hprime hp)).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj) :=
  DerivedCategory.Minus.ι.mapIso (rankOneDPDerivedFactorizationIso hprime.pos hp X) ≪≫
    (boundedAboveFlatDerivedBaseChangeIso (rankOneDPTruncatedMap hprime.pos hp).toRingHom
      (rankOneDPTruncatedRingHom_flat hprime hp)).app _

/-- 全次数の実ホモロジーは、切断多項式側の実ホモロジーの通常係数拡大で計算できる。 -/
def rankOneDPDerivedHomologyIso (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) ≅
      (ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso (rankOneDPDerivedFlatFactorizationIso hprime hp X) ≪≫
    (flatDerivedBaseChangeHomologyNatIso (rankOneDPTruncatedMap hprime.pos hp).toRingHom
      (rankOneDPTruncatedRingHom_flat hprime hp) n).app _

/-- 忠実平坦性により、分冪代数への実導来拡大は切断多項式側の各ホモロジーの零性を反映する。 -/
theorem rankOneDPDerivedHomology_isZero_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
      (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
  let Y := (((boundedAboveDerivedBaseChange q₀).obj X).obj)
  have h := faithfullyFlatDerivedHomology_map_eq_zero_iff
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom
    (rankOneDPTruncatedRingHom_faithfullyFlat hprime hp) n
    (𝟙 Y)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id] at h
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      ((flatDerivedBaseChange (rankOneDPTruncatedMap hprime.pos hp).toRingHom
        (rankOneDPTruncatedRingHom_flat hprime hp)).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
    simpa only [IsZero.iff_id_eq_zero] using h
  exact ((DerivedCategory.homologyFunctor _ n).mapIso
    (rankOneDPDerivedFlatFactorizationIso hprime hp X)).isZero_iff.trans hz

end SerrePositivity.BhattScholze

end RankOneDPDerivedFactorization

/-! ## 分冪代数への実導来係数拡大のKoszul判定

通常テンソルへの置換には、明示した実Koszulホモロジーの消滅を用いる。
-/

@[expose] public noncomputable section RankOneDPDerivedKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 切断多項式側の全ホモロジーを制限した加群は、実Koszul coneのホモロジーと一致する。 -/
def rankOneDPTruncationHomologyKoszulIso
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj) ≅
      (ModuleCat.restrictScalars q₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      (rankOneDPTruncationDerivedKoszulIso p X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q₀ n).app _

/-- 実分冪導来拡大の各ホモロジーは、X^pの実Koszul coneと同時に零になる。 -/
theorem rankOneDPDerivedKoszulHomology_isZero_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj)) := by
  have hr : IsZero ((ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
    simp only [ModuleCat.isZero_iff_subsingleton]
    rfl
  exact (rankOneDPDerivedHomology_isZero_iff hprime hp X n).trans
    ((rankOneDPTruncationHomologyKoszulIso (p := p) X n).isZero_iff.trans hr).symm

/-- 全高次Tor消滅は、具体的なX^p Koszul coneの負次ホモロジー消滅で判定できる。 -/
theorem rankOneDPScalarExtensionTorVanishing_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (M : ModuleCat.{u} P₀) :
    scalarExtensionTorVanishing (rankOneDPPolynomialMap A).toRingHom M ↔
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj M).obj)) := by
  change (∀ n : ℕ, 0 < n → IsZero
    (((Tor (ModuleCat.{u} P₀) n).obj
      (baseChangeScalarModule (rankOneDPPolynomialMap A).toRingHom)).obj M)) ↔ _
  rw [← derivedModuleBaseChange_negative_homology_vanishes_iff]
  apply forall₂_congr
  intro n _
  exact ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso
        (rankOneDPPolynomialMap A).toRingHom M)).isZero_iff.symm.trans
    (rankOneDPDerivedKoszulHomology_isZero_iff hprime hp
      (boundedAboveDerivedSingleFunctor.obj M) (-(n : ℤ)))

/-- 明示したKoszul消滅の下で、実分冪導来拡大の標準augmentationは通常テンソルへの同型。 -/
def rankOneDPDerivedOrdinaryIso_of_koszul (hprime : p.Prime) (hp : (p : A) = 0)
    (M : ModuleCat.{u} P₀)
    (hK : ∀ n : ℕ, 0 < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
          (boundedAboveDerivedSingleFunctor.obj M).obj))) :
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
        (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.extendScalars (rankOneDPPolynomialMap A).toRingHom).obj M) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ M
    ((rankOneDPScalarExtensionTorVanishing_iff hprime hp M).mpr hK)

end SerrePositivity.BhattScholze

end RankOneDPDerivedKoszul

/-! ## 切断多項式作用による分冪テンソルの相対平坦性 -/

@[expose] public noncomputable section RankOneDPTruncatedTensorFlat

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "G₀" => DividedPowerAlgebra A A

/-- 実切断多項式作用での分冪テンソルは、元のA作用を保ってMの可算直和と同値。 -/
def rankOneDPTruncatedTensorEquiv (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    (G₀ ⊗[C₀] M) ≃ₗ[A] (ℕ →₀ M) := by
  letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  letI : IsScalarTower A C₀ G₀ := rankOneDPTruncated_isScalarTower hprime.pos hp
  exact ((TensorProduct.congr (rankOneDPTruncatedEquiv hprime hp).symm
      (LinearEquiv.refl C₀ M)).trans
    ((TensorProduct.finsuppLeft C₀ C₀ C₀ M ℕ).trans
      (Finsupp.mapRange.linearEquiv (TensorProduct.lid C₀ M)))).restrictScalars A

/-- 指定された自由基底元との純テンソルは、対応する一項係数族へ写る。 -/
theorem rankOneDPTruncatedTensorEquiv_generator (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] (k : ℕ) (m : M) :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedTensorEquiv hprime hp M
      (DividedPowerAlgebra.dp A (p * k) (1 : A) ⊗ₜ[C₀] m) = Finsupp.single k m := by
  let : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower A C₀ G₀ := rankOneDPTruncated_isScalarTower hprime.pos hp
  have he : (rankOneDPTruncatedEquiv hprime hp).symm
      (DividedPowerAlgebra.dp A (p * k) (1 : A)) = Finsupp.single k (1 : C₀) := by
    apply (rankOneDPTruncatedEquiv hprime hp).injective
    rw [LinearEquiv.apply_symm_apply, rankOneDPTruncatedEquiv_single, one_smul]
  simp only [rankOneDPTruncatedTensorEquiv, LinearEquiv.restrictScalars_apply,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, he]
  ext i
  simp only [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
    TensorProduct.finsuppLeft_apply_tmul_apply, TensorProduct.lid_tmul]
  change (Finsupp.single k (1 : C₀)) i • m = (Finsupp.single k m) i
  by_cases hi : i = k
  · subst i
    simp only [Finsupp.single_eq_same, one_smul]
  · simp only [Finsupp.single_eq_of_ne hi, zero_smul]

/-- 切断多項式作用による実分冪テンソルは、元の係数環上の平坦性を保存・反映する。 -/
theorem rankOneDPTruncatedTensor_flat_iff (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Flat A (G₀ ⊗[C₀] M) ↔ Module.Flat A M := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  have hf : Module.Flat A (ℕ →₀ M) ↔ Module.Flat A M := by
    rw [Module.Flat.equiv_iff (finsuppLEquivDirectSum A M ℕ), Module.Flat.directSum_iff]
    simp only [forall_const]
  exact (Module.Flat.equiv_iff (rankOneDPTruncatedTensorEquiv hprime hp M)).trans hf

end SerrePositivity.BhattScholze

end RankOneDPTruncatedTensorFlat

/-! ## 分冪導来拡大の実ホモロジーの相対平坦性 -/

@[expose] public noncomputable section RankOneDPDerivedRelativeFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 実係数拡大を元の係数環へ制限した加群は、元の制限加群の可算直和と同値。 -/
def rankOneDPTruncatedExtensionEquiv (M : ModuleCat.{u} C₀) :
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj M)) ≃ₗ[A]
      (ℕ →₀ ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M)) := by
  let : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  let : Module A M := Module.compHom M (algebraMap A C₀)
  let : IsScalarTower A C₀ M := IsScalarTower.of_compHom A C₀ M
  let e := rankOneDPTruncatedTensorEquiv hprime hp M
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a z
  have hact : ∀ z : G₀ ⊗[C₀] M, (algebraMap A G₀ a) • z = a • z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul g m =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        congr 1
        exact (Algebra.smul_def a g).symm
    | add z w hz hw => simp only [smul_add, hz, hw]
  change e ((algebraMap A G₀ a) • z) = a • e z
  rw [hact, e.map_smul]

/-- 実係数拡大は、係数制限で明示したA平坦性を保存・反映する。 -/
theorem rankOneDPTruncatedExtension_flat_iff (M : ModuleCat.{u} C₀) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj M)) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) := by
  have hf : Module.Flat A (ℕ →₀ ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M)) ↔
      Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) := by
    rw [Module.Flat.equiv_iff
      (finsuppLEquivDirectSum A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) ℕ),
      Module.Flat.directSum_iff]
    simp only [forall_const]
  exact (Module.Flat.equiv_iff (rankOneDPTruncatedExtensionEquiv hprime hp M)).trans hf

include hprime hp in
/-- 分冪代数への実導来拡大の各ホモロジーのA平坦性は、切断多項式側と同値。 -/
theorem rankOneDPDerivedHomology_flat_iff
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) :=
  (Module.Flat.equiv_iff
    (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso
      (rankOneDPDerivedHomologyIso hprime hp X n)).toLinearEquiv)).trans
    (rankOneDPTruncatedExtension_flat_iff hprime hp _)

/-- 実Koszulホモロジーの比較は、元のA係数作用を保つ線形同値でもある。 -/
def rankOneDPTruncationKoszulRelativeHomologyEquiv
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀
          ((Polynomial.X : P₀) ^ p)).obj X.obj))) ≃ₗ[A]
    ((ModuleCat.restrictScalars (algebraMap A C₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) :=
  (((ModuleCat.restrictScalars (algebraMap A P₀)).mapIso
    (rankOneDPTruncationHomologyKoszulIso (p := p) X n)).toLinearEquiv)

include hprime hp in
/-- 実分冪導来拡大の各ホモロジーのA平坦性は、実X^p KoszulホモロジーのA平坦性と同値。 -/
theorem rankOneDPDerivedKoszulHomology_flat_iff
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj))) :=
  (rankOneDPDerivedHomology_flat_iff hprime hp X n).trans
    (Module.Flat.equiv_iff (rankOneDPTruncationKoszulRelativeHomologyEquiv X n)).symm

end SerrePositivity.BhattScholze

end RankOneDPDerivedRelativeFlat

/-! ## 具体的評価環の実導来比較とKoszul平坦性 -/

@[expose] public noncomputable section RankOneDPEvaluatedDerivedFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard rankOneDPPolynomialAlgebra
variable {p : ℕ} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A

/-- 実係数拡大をAへ制限した加群と、元の係数作用を持つ評価テンソル環の線形同値。 -/
def rankOneDPEvaluatedScalarExtensionEquiv (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPPolynomialMap A).toRingHom).obj
        (ModuleCat.of P₀ B))) ≃ₗ[A] RankOneDPEvaluatedEnvelope A B y := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  refine
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
  intro a z
  induction z using TensorProduct.inductionOn (R := P₀) (M := G₀) (N := B) with
  | tmul g b =>
      change ((algebraMap A G₀ a) * (g : G₀)) ⊗ₜ[P₀] (b : B) =
        (a • (g : G₀)) ⊗ₜ[P₀] (b : B)
      rw [Algebra.smul_def]
  | add z w hz hw => simp only [smul_add, hz, hw]

/-- 実導来分冪拡大のH0は、元のA作用を保って通常評価環と一致する。 -/
def rankOneDPEvaluatedDerivedH0Equiv (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) 0).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))).obj))) ≃ₗ[A]
      RankOneDPEvaluatedEnvelope A B y := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  let eH := (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) 0).mapIso
      (boundedAboveDerivedBaseChangeModuleIso (rankOneDPPolynomialMap A).toRingHom
        (ModuleCat.of P₀ B)) ≪≫
    (derivedModuleBaseChangeH0Iso (rankOneDPPolynomialMap A).toRingHom).app (ModuleCat.of P₀ B)
  exact (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso eH).toLinearEquiv).trans
    (rankOneDPEvaluatedScalarExtensionEquiv y)

/-- 通常評価環のA平坦性は、実X^p Koszul H0のA平坦性と同値。 -/
theorem rankOneDPEvaluatedEnvelope_flat_iff_koszul_h0
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    Module.Flat A (RankOneDPEvaluatedEnvelope A B y) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) 0).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact (Module.Flat.equiv_iff (rankOneDPEvaluatedDerivedH0Equiv y)).symm.trans
    (rankOneDPDerivedKoszulHomology_flat_iff hprime hp
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)) 0)

/-- 実Koszul消滅を仮定したときの、実導来評価環から通常評価環への標準比較同型。 -/
def rankOneDPEvaluatedDerivedOrdinaryIso (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hK : letI := rankOneDPEvaluationAlgebra (A := A) y
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of G₀ (RankOneDPEvaluatedEnvelope A B y)) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPDerivedOrdinaryIso_of_koszul hprime hp (ModuleCat.of P₀ B) hK

end SerrePositivity.BhattScholze

end RankOneDPEvaluatedDerivedFlat

/-! ## 標数pの実分冪導来拡大と実導来完備化

既存の標準完備化単位を使用する。混標数の古典的完備化への置換は含めない。
-/

@[expose] public noncomputable section RankOneDPCharacteristicCompletion

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A

/-- 標数pでは、P→Γへの任意の上有界実導来係数拡大は既に実導来p完備。 -/
theorem rankOneDPDerived_isComplete (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    DerivedCompletion.IsComplete G₀ (p : G₀)
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) := by
  have hpG : (p : G₀) = 0 := by
    rw [← map_natCast (algebraMap A G₀), hp, map_zero]
  apply DerivedCompletion.isComplete_of_scalar_pow_zero G₀ (p : G₀) _ 1
  rw [pow_one, hpG, zero_smul]

/-- 実導来p完備化は、標準完備化単位の逆により元の分冪導来拡大と同定される。 -/
def rankOneDPCharacteristicCompletionIso (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    (DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) ≅
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) :=
  (DerivedCompletion.derivedComplexCompletionUnitIso G₀ (p : G₀) _
    (rankOneDPDerived_isComplete hp X)).symm

/-- 標準完備化比較は、実導来ホモロジーの各次数を保つ。 -/
def rankOneDPCharacteristicCompletionHomologyIso (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
          (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) :=
  (DerivedCategory.homologyFunctor _ n).mapIso (rankOneDPCharacteristicCompletionIso hp X)

/-- 実導来p完備化後も、各ホモロジーの零性は実X^p Koszulホモロジーで判定できる。 -/
theorem rankOneDPCharacteristicCompletionHomology_isZero_iff
    (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj)) :=
  (rankOneDPCharacteristicCompletionHomologyIso hp X n).isZero_iff.trans
    (rankOneDPDerivedKoszulHomology_isZero_iff hprime hp X n)

/-- 実導来p完備化後の各ホモロジーのA平坦性も、実KoszulホモロジーのA平坦性と同値。 -/
theorem rankOneDPCharacteristicCompletionHomology_flat_iff
    (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        ((DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
          (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj))) :=
  (Module.Flat.equiv_iff (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso
    (rankOneDPCharacteristicCompletionHomologyIso hp X n)).toLinearEquiv)).trans
    (rankOneDPDerivedKoszulHomology_flat_iff hprime hp X n)

/-- 具体的評価代数のKoszul消滅の下、実導来p完備化も通常評価環の次数零対象と一致する。 -/
def rankOneDPEvaluatedCompletedOrdinaryIso {B : Type u} [CommRing B] [Algebra A B]
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hK : letI := rankOneDPEvaluationAlgebra (A := A) y
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)).obj))) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    (DerivedCompletion.derivedComplexCompletionFunctor G₀ (p : G₀)).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))).obj) ≅
      (boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of G₀ (RankOneDPEvaluatedEnvelope A B y))).obj := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPCharacteristicCompletionIso hp _ ≪≫
    DerivedCategory.Minus.ι.mapIso (rankOneDPEvaluatedDerivedOrdinaryIso hprime hp y hK)

end SerrePositivity.BhattScholze

end RankOneDPCharacteristicCompletion
