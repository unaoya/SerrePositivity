module
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialSubring
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialCoefficients
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.Injectivity

public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
public import SerrePositivity.BhattScholze.Delta.Division.Residue
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import Mathlib.RingTheory.Polynomial.Quotient
public import SerrePositivity.BhattScholze.Andre.Envelope.JetKoszul
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivisionCompletion
public import Mathlib.RingTheory.AdicCompletion.Basic
public import SerrePositivity.BhattScholze.Delta.DividedPower.Principal.PrincipalDP
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# p で割る δ 除算 A{φ(y)/p}：正則性・Koszul 分解・pd 包との同型（BS 著者版 Corollary 2.39 の r = 1）

## 概要
一元 p 除算の有限段の関係が非零因子で全有限 δ 関係商が p 正則であること、有限評価関係列の Koszul 分解と通常商との比較、生の包の p 正則性・A[1/p] への埋め込み・分冪構造（階乗の商と一致）・階乗生成部分環との同型・分冪表示環との A 代数同型 `deltaPDivisionRawPrincipalEquiv`、mod p と導来完備化の比較、逐次 Koszul 極限、二入力・二段の包の p 正則性。

## 方針
原典の BS 著者版 Corollary 2.39 を r = 1 で、生の包そのものが p ねじれなしで pd 包と同型という原典の形で示す。二元の場合の計算も含む。一般の有限正則列は BS 著者版 Lemma 2.38 の系列で扱う。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/FamilyEvaluation`、`Envelope/PDivisionSource`、`Envelope/RootFamilyRaw`、`Envelope/RootResidueKoszul`、`PowerRootEnvelope/DeltaDivisionWitt`、`Variants/RootedExtension`。
-/

universe u v

/-! ## 最初のδ像を加えたp除算関係商のp正則性

指定した一つの関係とその最初のδ像を扱う。全δ閉包への移行は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionSecondRelationRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => D.frobeniusLift (y s)
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 0
local notation "g₁" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 1
local notation "J₀" => Ideal.span {(p : L₀), g₀}
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "I₀" => Ideal.span {(p : A), a₀}
local notation "R₀" => L₀ ⧸ Ideal.span {g₀}

/-- 最初の関係をmod pで課すイデアルは、係数側の(p,φ(y_s))の拡大。 -/
theorem deltaPDivisionFirstPairIdeal_eq_map :
    J₀ = (I₀).map (MvPolynomial.C : A →+* L₀) := by
  change Ideal.span {(p : L₀), (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
    MvPolynomial.C (a₀))} = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    map_natCast (MvPolynomial.C : A →+* L₀) p, sub_eq_add_neg,
    Ideal.span_pair_left_mul_add, Ideal.span_pair_neg]

/-- L/(p,g_s)は係数商上の多項式環。 -/
def deltaPDivisionFirstPairPolynomialEquiv :
    (L₀ ⧸ J₀) ≃+* MvPolynomial (σ × ℕ) (A ⧸ I₀) :=
  (Ideal.quotEquivOfEq (deltaPDivisionFirstPairIdeal_eq_map D y s)).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial I₀).symm.toRingEquiv

/-- 係数商多項式表示は元の自由環の標準商像と両立する。 -/
theorem deltaPDivisionFirstPairPolynomialEquiv_mk (f : L₀) :
    deltaPDivisionFirstPairPolynomialEquiv D y s (q₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk I₀) f := by
  rw [deltaPDivisionFirstPairPolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk I₀))
    MvPolynomial.X f = MvPolynomial.map (Ideal.Quotient.mk I₀) f
  rw [← MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 最初のδ像の実mod(p,g_s)像は、単元係数1の冪関係。 -/
theorem deltaPDivisionSecondRelation_residue :
    q₀ g₁ = (q₀ (MvPolynomial.X (s, 0))) ^ p - q₀ (MvPolynomial.C (D.delta (a₀))) := by
  let F := relativeFreeDeltaStructure σ D
  have hp : q₀ (p : L₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))
  have hd : q₀ (MvPolynomial.C (p : A)) = 0 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact hp
  have hzero : q₀ g₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have ha : q₀ (MvPolynomial.C (a₀)) = 0 := by
    change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) - MvPolynomial.C (a₀)) = 0 at hzero
    rw [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] at hzero
    exact hzero
  have hδp : q₀ (F.delta (MvPolynomial.C (p : A))) = 1 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact F.map_delta_prime_of_zero q₀ hp
  have h := deltaDivisionFirstRelation_delta_image F q₀
    (MvPolynomial.C (p : A)) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a₀)) hp hd ha
  rw [hδp, one_mul, relativeFreeDeltaStructure_delta_C] at h
  exact h

/-- 最初のδ像はL/(p,g_s)上で正則。係数環の正則性・完備性は不要。 -/
theorem deltaPDivisionSecondRelation_residue_isSMulRegular :
    IsSMulRegular (L₀ ⧸ J₀) (q₀ g₁) := by
  let e := deltaPDivisionFirstPairPolynomialEquiv D y s
  have he : e (q₀ g₁) = MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C (Ideal.Quotient.mk I₀ (D.delta (a₀))) := by
    rw [deltaPDivisionSecondRelation_residue, map_sub, map_pow,
      deltaPDivisionFirstPairPolynomialEquiv_mk, deltaPDivisionFirstPairPolynomialEquiv_mk,
      MvPolynomial.map_X, MvPolynomial.map_C]
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun _ : σ × ℕ ↦ Ideal.Quotient.mk I₀ (D.delta (a₀))) (s, 0)
  change IsSMulRegular (MvPolynomial (σ × ℕ) (A ⧸ I₀))
    (MvPolynomial.X (s, 0) ^ p - MvPolynomial.C (Ideal.Quotient.mk I₀ (D.delta (a₀)))) at hr
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 先にg_sを課した環のmod p商と、L/(p,g_s)の既存二重商比較。 -/
def deltaPDivisionFirstQuotientModPEquiv :
    (R₀ ⧸ Ideal.span {(p : R₀)}) ≃+* (L₀ ⧸ J₀) :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : R₀)} =
    (Ideal.span {(p : L₀)}).map (Ideal.Quotient.mk (Ideal.span {g₀})) from by
      rw [Ideal.map_span, Set.image_singleton,
        map_natCast (Ideal.Quotient.mk (Ideal.span {g₀})) p])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {g₀}) (Ideal.span {(p : L₀)})).trans
      (Ideal.quotEquivOfEq ((sup_comm _ _).trans (Ideal.span_insert (p : L₀) {g₀}).symm)))

/-- 二重商比較は自由環の標準像を保つ。 -/
theorem deltaPDivisionFirstQuotientModPEquiv_mk (f : L₀) :
    deltaPDivisionFirstQuotientModPEquiv D y s
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {g₀}) f)) = q₀ f := by
  rw [deltaPDivisionFirstQuotientModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq _)
    (DoubleQuot.quotQuotEquivQuotSup _ _ (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- g_s商のmod p上でも、最初のδ像の標準像は正則。 -/
theorem deltaPDivisionSecondRelation_firstQuotient_mod_p_isSMulRegular :
    IsSMulRegular (R₀ ⧸ Ideal.span {(p : R₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
        (Ideal.Quotient.mk (Ideal.span {g₀}) g₁)) := by
  let e := deltaPDivisionFirstQuotientModPEquiv D y s
  intro x z hxz
  apply e.injective
  apply deltaPDivisionSecondRelation_residue_isSMulRegular D y s
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
      (Ideal.Quotient.mk (Ideal.span {g₀}) g₁)) = q₀ g₁ :=
    deltaPDivisionFirstQuotientModPEquiv_mk D y s g₁
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 最初の関係とそのδ像の実通常商に、新しいpねじれは生じない。 -/
theorem deltaPDivisionSecondRelation_quotient_p_mul_injective
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (y s))) :
    Function.Injective (fun x : L₀ ⧸ Ideal.span {g₀, g₁} ↦ (p : L₀ ⧸ Ideal.span {g₀, g₁}) * x) := by
  let r₁ := Ideal.Quotient.mk (Ideal.span {g₀}) g₁
  have hpR : IsSMulRegular R₀ (p : R₀) :=
    deltaPDivisionFirstRelation_quotient_p_mul_injective D y s hpA hy
  have hr := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod R₀ (p : R₀) r₁ hpR
    (deltaPDivisionSecondRelation_firstQuotient_mod_p_isSMulRegular D y s)
  have hpQ : IsSMulRegular (R₀ ⧸ Ideal.span {r₁}) (p : R₀ ⧸ Ideal.span {r₁}) :=
    Eq.mp (congrArg (fun c : R₀ ⧸ Ideal.span {r₁} ↦ IsSMulRegular (R₀ ⧸ Ideal.span {r₁}) c)
      (map_natCast (Ideal.Quotient.mk (Ideal.span {r₁})) p)) hr
  let e : (R₀ ⧸ Ideal.span {r₁}) ≃+* (L₀ ⧸ Ideal.span {g₀, g₁}) :=
    (Ideal.quotEquivOfEq (show Ideal.span {r₁} =
      (Ideal.span {g₁}).map (Ideal.Quotient.mk (Ideal.span {g₀})) from by
        rw [Ideal.map_span, Set.image_singleton])).trans
      ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {g₀}) (Ideal.span {g₁})).trans
        (Ideal.quotEquivOfEq (Ideal.span_insert g₀ {g₁}).symm))
  intro x z hxz
  apply e.symm.injective
  apply hpQ
  have h := congrArg e.symm hxz
  simpa only [smul_eq_mul, map_mul, map_natCast] using h

end SerrePositivity.BhattScholze

end DeltaPDivisionSecondRelationRegular

/-! ## 一元p除算の全有限δ関係商のp正則性

単元δ(p)と既存Witt正規化のghost単射を明示する。
元族全体のCFF拡大・完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteStageRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 一元p除算の深さ0イデアルは、最初の実関係の主イデアル。 -/
theorem deltaPDivisionFiniteStageIdeal_zero : I₀ 0 = Ideal.span {g₀ 0} := by
  unfold deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    have hn : n = 0 := Fin.ext (by omega)
    subst s
    subst n
    exact Set.mem_singleton _
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨((default : σ), 0), rfl⟩

/-- 一元の次の有限段は一つの実δ関係を追加して得られる。 -/
theorem deltaPDivisionFiniteStageIdeal_succ (N : ℕ) :
    I₀ (N + 1) = I₀ N ⊔ Ideal.span {g₀ (N + 1)} := by
  rw [deltaDivisionFiniteRelationIdeal_succ]
  congr 1
  congr 1
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact Set.mem_singleton _
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨(default : σ), rfl⟩

/-- 深さ1イデアルは、最初の実関係とその最初のδ像で生成される。 -/
theorem deltaPDivisionFiniteStageIdeal_one : I₀ 1 = Ideal.span {g₀ 0, g₀ 1} := by
  rw [deltaPDivisionFiniteStageIdeal_succ, deltaPDivisionFiniteStageIdeal_zero]
  exact (Ideal.span_insert (g₀ 0) {g₀ 1}).symm

/-- 有限段の通常商のmod pを、既存の実mod(p,d)商(d=p)へ移す二重商同型。 -/
def deltaPDivisionFiniteStageModPEquiv (N : ℕ) :
    ((L₀ ⧸ I₀ N) ⧸ Ideal.span {(p : L₀ ⧸ I₀ N)}) ≃+*
      (L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C (p : A)} ⊔ I₀ N)) := by
  have hbase : Ideal.span {(p : L₀), MvPolynomial.C (p : A)} = Ideal.span {(p : L₀)} := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : L₀)))
  exact (Ideal.quotEquivOfEq (show Ideal.span {(p : L₀ ⧸ I₀ N)} =
      (Ideal.span {(p : L₀)}).map (Ideal.Quotient.mk (I₀ N)) from by
        rw [Ideal.map_span, Set.image_singleton, map_natCast (Ideal.Quotient.mk (I₀ N)) p])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (I₀ N) (Ideal.span {(p : L₀)})).trans
      (Ideal.quotEquivOfEq ((sup_comm _ _).trans
        (congrArg (fun J : Ideal L₀ ↦ J ⊔ I₀ N) hbase.symm))))

omit [Unique σ] in
/-- 有限段の二重商比較は元の自由環の標準像を保つ。 -/
theorem deltaPDivisionFiniteStageModPEquiv_mk (N : ℕ) (f : L₀) :
    deltaPDivisionFiniteStageModPEquiv (σ := σ) D y N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (I₀ N) f)) = Ideal.Quotient.mk _ f := by
  rw [deltaPDivisionFiniteStageModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq _)
    (DoubleQuot.quotQuotEquivQuotSup _ _ (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
include hpA hg hv

/-- 次の実δ関係は、前段通常商のmod p上で正則。 -/
theorem deltaPDivisionFiniteStage_next_mod_p_isSMulRegular (N : ℕ) :
    IsSMulRegular ((L₀ ⧸ I₀ (N + 1)) ⧸ Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
      (Ideal.Quotient.mk (Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
        (Ideal.Quotient.mk (I₀ (N + 1)) (g₀ (N + 2)))) := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hr := deltaDivisionFiniteNextJet_quotient_isSMulRegular
    D hpA hpL hg (p : A) a₀ v hv N (default : σ)
  let e := deltaPDivisionFiniteStageModPEquiv (σ := σ) D y (N + 1)
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
      (Ideal.Quotient.mk (I₀ (N + 1)) (g₀ (N + 2)))) =
      Ideal.Quotient.mk _ (g₀ (N + 2)) := deltaPDivisionFiniteStageModPEquiv_mk (σ := σ) D y _ _
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 一元p除算のすべての有限実関係商はp正則。
単元δ(p)とghost単射は中間入力として明示する。 -/
theorem deltaPDivisionFiniteStage_quotient_p_mul_injective
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    Function.Injective (fun x : L₀ ⧸ I₀ N ↦ (p : L₀ ⧸ I₀ N) * x) := by
  have transport (J K : Ideal L₀) (hJK : J = K)
      (hK : IsSMulRegular (L₀ ⧸ K) (p : L₀ ⧸ K)) :
      IsSMulRegular (L₀ ⧸ J) (p : L₀ ⧸ J) := by
    subst K
    exact hK
  induction N using Nat.twoStepInduction with
  | zero =>
    exact transport _ _ (deltaPDivisionFiniteStageIdeal_zero (σ := σ) D y)
      (deltaPDivisionFirstRelation_quotient_p_mul_injective D
        (fun _ : σ ↦ y) (default : σ) hpA hy)
  | one =>
    exact transport _ _ (deltaPDivisionFiniteStageIdeal_one (σ := σ) D y)
      (deltaPDivisionSecondRelation_quotient_p_mul_injective D
        (fun _ : σ ↦ y) (default : σ) hpA hy)
  | more n _ ih =>
    let r := Ideal.Quotient.mk (I₀ (n + 1)) (g₀ (n + 2))
    have hr := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod
      (L₀ ⧸ I₀ (n + 1)) (p : L₀ ⧸ I₀ (n + 1)) r ih
      (deltaPDivisionFiniteStage_next_mod_p_isSMulRegular (σ := σ) D y hpA hg v hv n)
    have hpQ : IsSMulRegular ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r})
        (p : (L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) :=
      Eq.mp (congrArg (fun c : (L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r} ↦
        IsSMulRegular ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) c)
          (map_natCast (Ideal.Quotient.mk (Ideal.span {r})) p)) hr
    let e : ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) ≃+* (L₀ ⧸ I₀ (n + 2)) :=
      (Ideal.quotEquivOfEq (show Ideal.span {r} =
        (Ideal.span {g₀ (n + 2)}).map (Ideal.Quotient.mk (I₀ (n + 1))) from by
          rw [Ideal.map_span, Set.image_singleton])).trans
        ((DoubleQuot.quotQuotEquivQuotSup (I₀ (n + 1)) (Ideal.span {g₀ (n + 2)})).trans
          (Ideal.quotEquivOfEq (deltaPDivisionFiniteStageIdeal_succ (σ := σ) D y (n + 1)).symm))
    intro x z hxz
    apply e.symm.injective
    apply hpQ
    have h := congrArg e.symm hxz
    simpa only [smul_eq_mul, map_mul, map_natCast] using h

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteStageRegular

/-! ## 一元rawδ p除算包のp正則性と旧ねじれ除去商との比較

有限実関係商の正則性をδ閉包へ移す。単元δ(p)とghost単射を明示する。
導来pushoutの離散性・完備化後のCFFとは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionRawRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀
local notation "J₀" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal (p : A) a₀)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "K₀" => RingHom.ker (algebraMap B₀ (Localization.Away (j₀ (p : A))))
include hpA hg hv hy

/-- 有限段でのp正則性から、実δ閉包イデアルのp飽和性を得る。 -/
theorem deltaPDivisionRaw_relationIdeal_p_saturated (f : L₀) (hf : (p : L₀) * f ∈ J₀) :
    f ∈ J₀ := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations] at hf ⊢
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _
    (deltaDivisionFiniteRelationIdeal_mono D (p : A) a₀).directed_le).mp hf
  have hpN := deltaPDivisionFiniteStage_quotient_p_mul_injective (σ := σ) D y hpA hg v hv hy N
  have hz : Ideal.Quotient.mk (I₀ N) f = 0 := by
    apply hpN
    change (p : L₀ ⧸ I₀ N) * Ideal.Quotient.mk (I₀ N) f = (p : L₀ ⧸ I₀ N) * 0
    rw [mul_zero, ← map_natCast (Ideal.Quotient.mk (I₀ N)) p, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup I₀ N) (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 一元rawδ添加環A{φ(y)/p}そのものはp正則（BS 著者版 Corollary 2.39 の一元の場合の p 正則性）。 -/
theorem deltaPDivisionRaw_p_mul_injective :
    Function.Injective (fun x : B₀ ↦ (p : B₀) * x) := by
  let q := Ideal.Quotient.mk J₀
  intro x z hxz
  change (p : B₀) * x = (p : B₀) * z at hxz
  apply sub_eq_zero.mp
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (x - z)
  have hpf : q ((p : L₀) * f) = 0 := by
    rw [map_mul, map_natCast, hf, mul_sub, hxz, sub_self]
  have hm := deltaPDivisionRaw_relationIdeal_p_saturated (σ := σ) D y hpA hg v hv hy f
    (Ideal.Quotient.eq_zero_iff_mem.mp hpf)
  exact hf.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm)

omit hv in
/-- 源がp進完備なら、δ(p)の単元性を既存のJacobson根基判定から内部で供給できる。 -/
theorem deltaPDivisionRaw_p_mul_injective_of_adicComplete
    [IsAdicComplete (Ideal.span {(p : A)}) A] :
    Function.Injective (fun x : B₀ ↦ (p : B₀) * x) := by
  have hdist := D.isDistinguished_p
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))
  obtain ⟨w, hw⟩ := hdist
  exact deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg w hw hy

/-- 同じ仮定で、y^p/pのrawδ添加環もp正則。証明済み平行移動同型で移す。 -/
theorem deltaPDivisionRawPower_p_mul_injective :
    Function.Injective (fun x : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p) ↦
      (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * x) := by
  let e := deltaPDivisionFrobeniusShiftEquiv D (fun _ : σ ↦ y)
  intro x z hxz
  change (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * x =
    (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * z at hxz
  apply e.symm.injective
  apply deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
  have h := congrArg e.symm hxz
  simpa only [map_mul, map_natCast] using h

/-- このrawδ包では旧p冪ねじれ、すなわちp局所化への核は既に零。 -/
theorem deltaPDivisionRaw_ker_away_eq_bot : K₀ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (j₀ (p : A))) (Localization.Away (j₀ (p : A))) x).mp hx
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : B₀) (j₀ (p : A))).mp m.property
  have hp : IsLeftRegular (j₀ (p : A)) := by
    intro z t hzt
    apply deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
    simpa only [map_natCast (j₀) p] using hzt
  apply Ideal.mem_bot.mpr
  apply hp.pow N
  change (j₀ (p : A)) ^ N * x = (j₀ (p : A)) ^ N * 0
  rw [hN, hm, mul_zero]

/-- 旧pねじれのδ閉包も零であり、ここでは除去商で環を変えない。 -/
theorem deltaPDivisionRaw_torsion_deltaClosure_eq_bot : (E₀).deltaClosure K₀ = ⊥ := by
  have hK := deltaPDivisionRaw_ker_away_eq_bot (σ := σ) D y hpA hg v hv hy
  have hstable : (E₀).IsStable (⊥ : Ideal B₀) := by
    intro x hx
    rw [Ideal.mem_bot] at hx ⊢
    rw [hx, DeltaStructure.delta_zero]
  exact (congrArg (E₀).deltaClosure hK).trans ((E₀).deltaClosure_eq hstable)

/-- 一元rawδ包と既存旧ねじれ除去商を標準商射で比較する具体的同型（BS 著者版 Corollary 2.39 の一元の場合の p 冪ねじれ除去との同定）。 -/
def deltaPDivisionRawTorsionEquiv : B₀ ≃+* DeltaDivisionTorsionQuotient D (p : A) a₀ :=
  (RingEquiv.quotientBot B₀).symm.trans (Ideal.quotEquivOfEq
    (deltaPDivisionRaw_torsion_deltaClosure_eq_bot (σ := σ) D y hpA hg v hv hy).symm)

/-- 同型は実際の旧ねじれ除去の標準商射。 -/
theorem deltaPDivisionRawTorsionEquiv_apply (x : B₀) :
    deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy x = Ideal.Quotient.mk _ x := by
  rw [deltaPDivisionRawTorsionEquiv, RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk,
    Ideal.quotEquivOfEq_mk]

/-- raw包と除去商の比較の両方向は既存δ構造と両立する。 -/
theorem deltaPDivisionRawTorsionEquiv_isDeltaHom :
    (E₀).IsDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀)
        (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).toRingHom ∧
      (deltaDivisionTorsionStructure D (p : A) a₀).IsDeltaHom E₀
        (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).symm.toRingHom := by
  let e := deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy
  have hf : (E₀).IsDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀) e.toRingHom := by
    intro x
    change e ((E₀).delta x) = (deltaDivisionTorsionStructure D (p : A) a₀).delta (e x)
    rw [deltaPDivisionRawTorsionEquiv_apply, deltaPDivisionRawTorsionEquiv_apply]
    exact ((E₀).isDeltaHom_quotient_mk _ ((E₀).isStable_deltaClosure _)) x
  refine ⟨hf, ?_⟩
  intro x
  apply e.injective
  change e (e.symm ((deltaDivisionTorsionStructure D (p : A) a₀).delta x)) =
    e ((E₀).delta (e.symm x))
  rw [RingEquiv.apply_symm_apply]
  have hfx : e ((E₀).delta (e.symm x)) =
      (deltaDivisionTorsionStructure D (p : A) a₀).delta (e (e.symm x)) := hf (e.symm x)
  rw [RingEquiv.apply_symm_apply] at hfx
  exact hfx.symm

/-- 比較同型は元の係数環からの実標準射を保つ。 -/
theorem deltaPDivisionRawTorsionEquiv_comp :
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).toRingHom.comp j₀ =
      deltaDivisionTorsionMap D (p : A) a₀ := by
  ext x
  change deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy (j₀ x) = _
  rw [deltaPDivisionRawTorsionEquiv_apply]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionRawRegular

/-! ## raw一元δ p除算包のA[1/p]への具体的埋め込み

既存の標準δ評価とp局所化比較を使う。実際の像部分環との同型も供給する。
分冪包との一致・完全忠実平坦性は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionRawEmbedding

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section General
variable {σ : Type v} (D : DeltaStructure p A) (a : σ → A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a
local notation "Bₚ" => Localization.Away (p : B₀)

/-- 具体的δ評価の像部分環は局所化上のδ作用で安定。単射性は不要。 -/
theorem deltaPDivisionToAway_range_delta_stable
    (x : Localization.Away (p : A)) (hx : x ∈ (deltaPDivisionToAway D a).range) :
    (deltaPDivisionAwayStructure D).delta x ∈ (deltaPDivisionToAway D a).range := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨(deltaAdjoinDivisionStructure D (p : A) a).delta b,
    (deltaPDivisionToAway_spec D a).1 b⟩
end General

section Shift
variable {σ : Type v} (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "a₀" => fun t ↦ D.frobeniusLift (y t)
local notation "f₀" => deltaPDivisionToAway D a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "v₀" => deltaAdjoinDivisionVariable D (p : A) a₀
local notation "Aₚ" => Localization.Away (p : A)

/-- φ(y)/pからδ(y)を引いた元の像は、A[1/p]内の具体的なy^p/p。 -/
theorem deltaPDivisionToAway_shifted_variable :
    f₀ (v₀ s - j₀ (D.delta (y s))) =
      IsLocalization.Away.invSelf (p : A) * (algebraMap A Aₚ (y s)) ^ p := by
  have hb : f₀ (j₀ (D.delta (y s))) = algebraMap A Aₚ (D.delta (y s)) :=
    RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 _
  have hi : IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (p : A) = 1 := by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]
  rw [map_sub, (deltaPDivisionToAway_spec D a₀).2.2, hb, D.frobeniusLift_apply,
    map_add, map_pow, map_mul, mul_add, ← mul_assoc, hi, one_mul, add_sub_cancel_right]
end Shift

section Unary
variable {σ : Type u} [Unique σ] (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "f₀" => deltaPDivisionToAway D a₀
local notation "Aₚ" => Localization.Away (p : A)
include hpA hg hv hy

/-- 明示した中間入力の下で、一元rawδ包A{φ(y)/p}はA[1/p]へ単射に写る（BS 著者版 Corollary 2.39 の一元の場合の A[1/p] への比較の単射性）。 -/
theorem deltaPDivisionRawToAway_injective : Function.Injective f₀ :=
  deltaPDivisionToAway_injective_of_p_mul_injective D a₀
    (deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy)

omit hv in
/-- 源がp進完備なら単元δ(p)の指定を省いた同じ具体的埋め込みを得る。 -/
theorem deltaPDivisionRawToAway_injective_of_adicComplete
    [IsAdicComplete (Ideal.span {(p : A)}) A] : Function.Injective f₀ :=
  deltaPDivisionToAway_injective_of_p_mul_injective D a₀
    (deltaPDivisionRaw_p_mul_injective_of_adicComplete (σ := σ) D y hpA hg hy)

/-- raw一元δ包を、A[1/p]内の具体的δ評価の像部分環と同定する。 -/
def deltaPDivisionRawRangeEquiv : B₀ ≃+* (f₀).range :=
  RingEquiv.ofBijective (f₀).rangeRestrict
    ⟨fun _ _ h ↦ deltaPDivisionRawToAway_injective (σ := σ) D y hpA hg v hv hy
      (congrArg Subtype.val h), (f₀).rangeRestrict_surjective⟩

/-- 部分環表示の値は実際のA[1/p]へのδ評価。 -/
theorem deltaPDivisionRawRangeEquiv_apply (b : B₀) :
    (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy b : Aₚ) = f₀ b := rfl

/-- 部分環表示は元のAからの標準射を保つ。 -/
theorem deltaPDivisionRawRangeEquiv_coeff (r : A) :
    (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy (j₀ r) : Aₚ) =
      algebraMap A Aₚ r := by
  rw [deltaPDivisionRawRangeEquiv_apply]
  exact RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 r
end Unary

end SerrePositivity.BhattScholze

end DeltaPDivisionRawEmbedding

/-! ## 正則一元raw包と具体的階乗生成部分環の標準同型

単射性の中間仮定を明示する。導来pushout比較・分冪包普遍性は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialEquiv

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
local notation "ys" => fun _ : σ ↦ y
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "L₀" => Localization.Away (p : A)
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

/-- 正則一元raw包と局所化内の具体的階乗生成部分環の標準環同型。 -/
def deltaPDivisionRawFactorialEquiv : B₀ ≃+* pDivisionFactorialSubring p ys :=
  (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy).trans
    (RingEquiv.subringCongr (pDivisionFactorialSubring_eq_raw_range hlocal D ys).symm)

include hpA hg hv hy hlocal

/-- 同型の値は既存の具体的δ評価そのもの。 -/
theorem deltaPDivisionRawFactorialEquiv_apply (b : B₀) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal b : L₀) =
      deltaPDivisionToAway D a₀ b := by
  rw [deltaPDivisionRawFactorialEquiv, RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply]
  exact deltaPDivisionRawRangeEquiv_apply (σ := σ) D y hpA hg v hv hy b

/-- 同型は元のAからの基底標準射を保つ。 -/
theorem deltaPDivisionRawFactorialEquiv_coeff (r : A) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal (j₀ r) : L₀) =
      algebraMap A L₀ r := by
  rw [deltaPDivisionRawFactorialEquiv_apply]
  exact RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 r

/-- 同型はraw包内の階乗分母を局所化内の標準階乗分母へ送る。 -/
theorem deltaPDivisionRawFactorialEquiv_factorial (s : σ) (n : ℕ) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal
      (deltaPDivisionRawFactorialQuotient D ys hlocal s n) : L₀) =
      pDivisionFactorialValue p ys s n := by
  rw [deltaPDivisionRawFactorialEquiv_apply]
  exact deltaPDivisionToAway_factorialQuotient D ys hlocal s n

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialEquiv

/-! ## 正則raw δ p除算包と分冪表示環の実A代数同型

既存の中間仮定を明示して通常環を比較する。導来pushout比較は含めない。
-/

@[expose] public noncomputable section DeltaPDivisionRawPrincipal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)

omit [Fact p.Prime] in
/-- 定数の一元入力では、階乗部分環は単一添字の宇宙レベルに依存しない。 -/
theorem deltaPDivisionUnaryFactorialSubring_eq :
    pDivisionFactorialSubring p (fun _ : σ ↦ y) =
      pDivisionFactorialSubring p (fun _ : Unit ↦ y) := by
  have hr : Set.range (fun z : σ × ℕ ↦
      pDivisionFactorialValue p (fun _ : σ ↦ y) z.1 z.2) =
      Set.range (fun z : Unit × ℕ ↦
        pDivisionFactorialValue p (fun _ : Unit ↦ y) z.1 z.2) := by
    ext z
    constructor
    · rintro ⟨⟨s, n⟩, rfl⟩
      exact ⟨((), n), rfl⟩
    · rintro ⟨⟨s, n⟩, rfl⟩
      exact ⟨((default : σ), n), rfl⟩
  unfold pDivisionFactorialSubring
  rw [hr]

/-- 同じ具体的階乗部分環を通る、raw δ p除算包と分冪表示環の標準環同型。 -/
def deltaPDivisionRawPrincipalEquiv : B₀ ≃+* PrincipalDPPresentation A y :=
  ((deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA).trans
    (RingEquiv.subringCongr (deltaPDivisionUnaryFactorialSubring_eq (p := p) (σ := σ) y))).trans
      (principalDPFactorialEquiv hA hpA D y hy).symm

/-- 標準環同型は、元のAからの全基底係数の像を保つ。 -/
theorem deltaPDivisionRawPrincipalEquiv_coeff (a : A) :
    deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy (j₀ a) =
      algebraMap A (PrincipalDPPresentation A y) a := by
  have hb : deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA (j₀ a) =
      pDivisionFactorialBase p (fun _ : σ ↦ y) a := by
    apply Subtype.ext
    exact deltaPDivisionRawFactorialEquiv_coeff (σ := σ) D y hpA hg v hv hy hA a
  rw [deltaPDivisionRawPrincipalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, hb]
  change (principalDPFactorialEquiv hA hpA D y hy).symm
    (pDivisionFactorialBase p (fun _ : Unit ↦ y) a) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply]

/-- 元の自然なA作用を保つ、raw δ p除算包と分冪表示環のA代数同型。 -/
def deltaPDivisionRawPrincipalAlgEquiv : B₀ ≃ₐ[A] PrincipalDPPresentation A y :=
  { deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy with
    commutes' := fun a ↦ deltaPDivisionRawPrincipalEquiv_coeff hA hpA D y hg v hv hy a }

/-- 全raw階乗生成元は、対応する表示環の標準分冪生成元へ写る。 -/
theorem deltaPDivisionRawPrincipalEquiv_factorial (n : ℕ) :
    deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy
      (deltaPDivisionRawFactorialQuotient D (fun _ : σ ↦ y) hA (default : σ) n) =
        principalDPGenerator y n := by
  have hb : deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA
      (deltaPDivisionRawFactorialQuotient D (fun _ : σ ↦ y) hA (default : σ) n) =
      (⟨pDivisionFactorialValue p (fun _ : σ ↦ y) (default : σ) n,
        pDivisionFactorialSubring_value_mem (fun _ : σ ↦ y) (default : σ) n⟩ :
        pDivisionFactorialSubring p (fun _ : σ ↦ y)) := by
    apply Subtype.ext
    exact deltaPDivisionRawFactorialEquiv_factorial (σ := σ) D y hpA hg v hv hy hA (default : σ) n
  rw [deltaPDivisionRawPrincipalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, hb]
  change (principalDPFactorialEquiv hA hpA D y hy).symm
    (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
      pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply]

end SerrePositivity.BhattScholze

end DeltaPDivisionRawPrincipal

/-! ## 任意先行族のraw p除算へ一入力を追加する正則性帰納 -/

@[expose] public noncomputable section DeltaPDivisionFamilyStep

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} {η : Type (max u v)}
  [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (y : σ → A) (x : A)
local notation "a" => fun s ↦ D.frobeniusLift (y s)
local notation "B" => DeltaAdjoinDivision D (p : A) a
local notation "E" => deltaAdjoinDivisionStructure D (p : A) a
local notation "j" => deltaAdjoinDivisionMap D (p : A) a

/-- 任意先行族のp正則raw包へ次の一入力を除算添加した実二段環はp正則。 -/
theorem deltaPDivisionFamilyStep_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : B ↦ (p : B) * z))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B) η) → ℕ → RelativeFreeDeltaRing (R := B) η))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : B)
      (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x)) ↦
      (p : DeltaAdjoinDivision E (p : B)
        (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x))) * z) := by
  let wB := w.map (j).toMonoidHom
  have hwB : (wB : B) = (E).delta (p : B) := by
    change j (w : A) = _
    rw [hw, deltaAdjoinDivisionMap_isDeltaHom D (p : A) a (p : A), map_natCast]
  exact deltaPDivisionRaw_p_mul_injective (σ := η) E (j x) hpB hg₁ wB hwB
    (deltaPDivisionRawModP_next_isSMulRegular D hpA hg₀ y w hw x hx)

/-- 任意先行族へ一入力を同時に加えたraw p除算包も、同じ具体的仮定でp正則。 -/
theorem deltaPDivisionFamilySum_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : B ↦ (p : B) * z))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B) η) → ℕ → RelativeFreeDeltaRing (R := B) η))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    Function.Injective (fun z : DeltaAdjoinDivision D (p : A)
      (Sum.elim a (fun _ : η ↦ D.frobeniusLift x)) ↦
      (p : DeltaAdjoinDivision D (p : A) (Sum.elim a (fun _ : η ↦ D.frobeniusLift x))) * z) := by
  let e := deltaAdjoinDivisionSumEquiv D (p : A) a (fun _ : η ↦ D.frobeniusLift x)
  have hφ : (fun _ : η ↦ j (D.frobeniusLift x)) =
      (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x)) := by
    funext t
    exact (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a).map_frobeniusLift x
  have hpT : Function.Injective (fun z : DeltaAdjoinDivision E (j (p : A))
      (fun _ : η ↦ j (D.frobeniusLift x)) ↦
      (p : DeltaAdjoinDivision E (j (p : A)) (fun _ : η ↦ j (D.frobeniusLift x))) * z) := by
    rw [map_natCast, hφ]
    exact deltaPDivisionFamilyStep_p_mul_injective (η := η) D y x hpA hpB hg₀ hg₁ w hw hx
  intro z t hzt
  apply e.injective
  apply hpT
  simpa only [map_mul, map_natCast] using congrArg e hzt

end SerrePositivity.BhattScholze

end DeltaPDivisionFamilyStep

/-! ## 二段のraw δ p除算包のp正則性

次の入力の係数商での正則性を用いて、一元除算のp正則性を二段へ延ばす。
自由δ環のghost単射は各段で明示的に仮定する。
-/

@[expose] public noncomputable section DeltaPDivisionTwoStep

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y₀ y₁ : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

omit [Unique σ] in
/-- 指定されたδ(p)の単元は、第一raw除算包でも同じδ(p)を与える。 -/
theorem deltaPDivisionRaw_delta_prime_unit_map
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    ((w.map j₀ : B₀ˣ) : B₀) = (E₀).delta (p : B₀) := by
  change j₀ (w : A) = _
  rw [hw, deltaAdjoinDivisionMap_isDeltaHom D (p : A) a₀ (p : A), map_natCast]

/-- y₁のA/(p,y₀^p)での正則性は第一raw包の実mod p商へ移る。 -/
theorem deltaPDivisionRaw_next_isSMulRegular
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)}) (j₀ y₁)) := by
  apply deltaPDivisionRawModP_next_isSMulRegular D hpA hg (fun _ : σ ↦ y₀) w hw y₁
  rw [deltaPDivisionFirstBaseIdeal_const_power (p := p) (σ := σ) y₀]
  exact hy₁

/-- 二段の具体的raw除算環はp正則。完備化や完全忠実平坦性は仮定・結論に含めない。 -/
theorem deltaPDivisionTwoStep_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) σ) → ℕ → RelativeFreeDeltaRing (R := B₀) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₀ : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y₀))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    Function.Injective (fun b : DeltaAdjoinDivision E₀ (p : B₀)
      (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁)) ↦
      (p : DeltaAdjoinDivision E₀ (p : B₀) (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁))) * b) := by
  exact deltaPDivisionRaw_p_mul_injective (σ := σ) E₀ (j₀ y₁)
    (deltaPDivisionRaw_p_mul_injective (σ := σ) D y₀ hpA hg₀ w hw hy₀)
    hg₁ (w.map j₀) (deltaPDivisionRaw_delta_prime_unit_map (σ := σ) D y₀ w hw)
    (deltaPDivisionRaw_next_isSMulRegular (σ := σ) D y₀ y₁ hpA hg₀ w hw hy₁)

end SerrePositivity.BhattScholze

end DeltaPDivisionTwoStep

/-! ## 二入力の同時raw p除算包のp正則性

二段除算との標準同型を通じてp正則性を移す。ghost単射は各段で仮定する。
-/

@[expose] public noncomputable section DeltaPDivisionPairRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y₀ y₁ : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y₀
local notation "a₁" => fun _ : σ ↦ D.frobeniusLift y₁
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "S" => DeltaAdjoinDivision D (p : A) (Sum.elim a₀ a₁)

/-- 二つのFrobenius入力の同時raw p除算包は、具体的な逐次正則性の仮定の下でp正則。 -/
theorem deltaPDivisionPair_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) σ) → ℕ → RelativeFreeDeltaRing (R := B₀) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₀ : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y₀))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    Function.Injective (fun s : S ↦ (p : S) * s) := by
  let e := deltaAdjoinDivisionSumEquiv D (p : A) a₀ a₁
  have hφ : (fun _ : σ ↦ j₀ (D.frobeniusLift y₁)) =
      (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁)) := by
    funext s
    exact (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a₀).map_frobeniusLift y₁
  have hpT : Function.Injective (fun t : DeltaAdjoinDivision E₀ (j₀ (p : A))
      (fun _ : σ ↦ j₀ (D.frobeniusLift y₁)) ↦
      (p : DeltaAdjoinDivision E₀ (j₀ (p : A)) (fun _ : σ ↦ j₀ (D.frobeniusLift y₁))) * t) := by
    rw [map_natCast, hφ]
    exact deltaPDivisionTwoStep_p_mul_injective (σ := σ) D y₀ y₁ hpA hg₀ hg₁ w hw hy₀ hy₁
  intro s t hst
  apply e.injective
  apply hpT
  simpa only [map_mul, map_natCast] using congrArg e hst

/-- 同じ仮定で、二つのp乗入力の同時raw p除算包もp正則。 -/
theorem deltaPDivisionPairPower_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) σ) → ℕ → RelativeFreeDeltaRing (R := B₀) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₀ : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y₀))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    Function.Injective (fun s : DeltaAdjoinDivision D (p : A)
      (fun t : σ ⊕ σ ↦ (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t) ^ p) ↦
      (p : DeltaAdjoinDivision D (p : A)
        (fun t : σ ⊕ σ ↦ (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t) ^ p)) * s) := by
  let e := deltaPDivisionFrobeniusShiftEquiv D
    (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁))
  have hφ : (fun s : σ ⊕ σ ↦ D.frobeniusLift
      (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) s)) = Sum.elim a₀ a₁ := by
    funext s
    cases s <;> rfl
  have hpφ : Function.Injective (fun s : DeltaAdjoinDivision D (p : A)
      (fun t : σ ⊕ σ ↦ D.frobeniusLift
        (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t)) ↦
      (p : DeltaAdjoinDivision D (p : A) (fun t : σ ⊕ σ ↦ D.frobeniusLift
        (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t))) * s) := by
    rw [hφ]
    exact deltaPDivisionPair_p_mul_injective (σ := σ) D y₀ y₁ hpA hg₀ hg₁ w hw hy₀ hy₁
  intro s t hst
  apply e.symm.injective
  apply hpφ
  simpa only [map_mul, map_natCast] using congrArg e.symm hst

end SerrePositivity.BhattScholze

end DeltaPDivisionPairRegular

/-! ## 実一元p除算関係の非零因子性

最高係数pの正則性と後続変数表示を用いる。mod pでの正則性だけからは結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteRelationsRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 最初の実p除算関係は、Aのp正則性だけで自由δ環上の非零因子。 -/
theorem deltaPDivisionFirstRelation_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) :
    IsSMulRegular L₀ (g₀ 0) := by
  exact deltaDivisionFirstRelation_isSMulRegular D (p : A) a₀ (default : σ) hpA

/-- 前段実関係商がp正則なら、次の実p除算関係はその商上で非零因子。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular (N : ℕ)
    (hpQ : Function.Injective (fun x : L₀ ⧸ I₀ N => (p : _) * x)) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) := by
  apply deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular D (p : A) a₀ N
    (default : σ)
  have hφ : ∀ n : ℕ, D.frobeniusLift^[n] (p : A) = p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  simpa only [hφ, map_natCast] using
    (show IsSMulRegular (L₀ ⧸ I₀ N) (p : L₀ ⧸ I₀ N) from hpQ)

/-- 正則な一元入力の全有限段で、次の実δ関係は通常商上の非零因子。
単元δ(p)とghost単射は既存p正則性の中間入力として保持する。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) :=
  deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular D y N
    (deltaPDivisionFiniteStage_quotient_p_mul_injective D y hpA hg v hv hy N)

/-- 全有限実関係列の生成イデアルは、既存の全有限段関係イデアル。 -/
theorem deltaPDivisionFiniteRelations_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) = I₀ N := by
  unfold Ideal.ofList deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- pを前置しない実δ関係列自身の弱正則性。 -/
theorem deltaPDivisionFiniteRelations_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin (N + 1) => g₀ i.val) := by
  induction N with
  | zero =>
      simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero] using
        (RingTheory.Sequence.isWeaklyRegular_singleton_iff L₀ (g₀ 0)).mpr
          (deltaPDivisionFirstRelation_isSMulRegular D y hpA)
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ :
          Submodule L₀ L₀) = I₀ N := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaPDivisionFiniteRelations_ofList]
      change IsSMulRegular (L₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ : Submodule L₀ L₀))
        (g₀ (N + 1))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ N)) (fun _ => rfl)).mp
        (deltaPDivisionFiniteStage_next_isSMulRegular D y hpA hg v hv hy N)

/-- 実δ関係g₀,…,g_NのKoszul複体は、実際の有限通常商の分解。
André・perfectoid化全射性の引用には依存しない。 -/
theorem deltaPDivisionFiniteRelations_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => g₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaPDivisionFiniteRelations_isWeaklyRegular D y hpA hg v hv hy N)

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteRelationsRegular

/-! ## 実p除算の有限評価関係列のKoszul分解

全prefixのイデアル一致を使い、実反復差関係列から評価関係列へ正則性を移す。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteEvaluationRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

variable [Unique σ] (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 一元評価関係の全有限prefixの生成イデアルは既存の実I_N。 -/
theorem deltaPDivisionFiniteEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) = I₀ N := by
  exact deltaDivisionFiniteEvaluation_ofList D (p : A) a₀ N

/-- 前段商での次の反復差関係の非零因子性は、次の評価関係へ移る。 -/
theorem deltaPDivisionFiniteEvaluation_next_isSMulRegular (N : ℕ)
    (hg : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1)))) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (h₀ (N + 1))) := by
  exact deltaDivisionFiniteEvaluation_next_isSMulRegular D (p : A) a₀ N hg

/-- 正則一元入力では、実評価関係の全有限列が弱正則。 -/
theorem deltaPDivisionFiniteEvaluation_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin (N + 1) => h₀ i.val) := by
  induction N with
  | zero =>
      have hr := deltaPDivisionFirstRelation_isSMulRegular (σ := σ) D y hpA
      rw [List.ofFn_succ, List.ofFn_zero,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      intro x z hxz
      apply hr
      change (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
        MvPolynomial.C (D.frobeniusLift y)) * x =
          (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
            MvPolynomial.C (D.frobeniusLift y)) * z
      change (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
        MvPolynomial.C (D.frobeniusLift y)) * x =
          (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
            MvPolynomial.C (D.frobeniusLift y)) * z at hxz
      exact hxz
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) • ⊤ :
          Submodule L₀ L₀) = I₀ N := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaPDivisionFiniteEvaluation_ofList]
      change IsSMulRegular (L₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) • ⊤ : Submodule L₀ L₀))
        (h₀ (N + 1))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ N)) (fun _ => rfl)).mp
        (deltaPDivisionFiniteEvaluation_next_isSMulRegular D y N
          (deltaPDivisionFiniteStage_next_isSMulRegular D y hpA hg v hv hy N))

/-- 実評価関係の有限Koszul複体は、実際の有限通常商を分解する。 -/
theorem deltaPDivisionFiniteEvaluation_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => h₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaPDivisionFiniteEvaluation_isWeaklyRegular D y hpA hg v hv hy N)

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteEvaluationRegular

/-! ## 実自由δ射に沿う有限源グラフ商のTor

P=A{x}からL=A{z}、x↦p zへ基底変更した有限源商を、実評価関係Koszul複体で計算する。
有限商を全源評価環Aと取り違えない。
-/

@[expose] public noncomputable section DeltaPDivisionSourceFiniteTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)

/-- 全深さ≤Nの、源評価核の具体的な有限グラフ列。 -/
def deltaPDivisionSourceGraphPrefix (N : ℕ) : Fin (N + 1) → P₀ :=
  fun i => deltaDivisionSourceGraphRelation D a₀ (default, i.val)

/-- 実源Pの有限グラフ関係商。全源評価環Aとはまだ同一視しない。 -/
abbrev DeltaPDivisionSourceFiniteQuotient (N : ℕ) :=
  P₀ ⧸ Ideal.span (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y N))

/-- 実源の各有限グラフ列のKoszul複体は、実有限源商の分解。 -/
theorem deltaPDivisionSourceGraphPrefix_isKoszulResolution (N : ℕ) :
    SerrePositivity.IsKoszulResolution (deltaPDivisionSourceGraphPrefix (σ := σ) D y N) := by
  apply deltaDivisionSourceGraph_fin_isKoszulResolution
  intro i j hij
  exact Fin.ext (congrArg Prod.snd hij)

/-- 実αに沿う実有限源商のTorと、終域の実評価関係Koszulホモロジーの比較。 -/
def deltaPDivisionSourceFiniteKoszulTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived i).obj
      (ModuleCat.of P₀ (DeltaPDivisionSourceFiniteQuotient (σ := σ) D y N)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (N + 1) =>
        deltaDivisionEvaluationRelation D (p : A) a₀ (default : σ) j.val)).homology (-(i : ℤ)) := by
  exact deltaDivisionSourceFiniteCoordinateKoszulTorIso D (p : A) a₀
    (fun j : Fin (N + 1) => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij)) i

/-- 正則一元入力では、実αに沿う有限源商の全正次数Torが零。 -/
theorem deltaPDivisionSourceFinite_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1)
      (DeltaPDivisionSourceFiniteQuotient (σ := σ) D y N)) := by
  exact deltaDivisionSourceFiniteCoordinate_tor_subsingleton D (p : A) a₀
    (fun j : Fin (N + 1) => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))
    (deltaPDivisionFiniteEvaluation_isKoszulResolution D y hpA hg v hv hy N) i

end SerrePositivity.BhattScholze

end DeltaPDivisionSourceFiniteTor

/-! ## rawφ除算包の分冪構造と既存の階乗分母

正則一元入力の仮定を明示する。分冪包の普遍性・CFFは別工程。
-/

@[expose] public noncomputable section DeltaPDivisionDividedPowers

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "ys" => fun _ : σ ↦ y
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

/-- rawφ除算包の各基底元j(y)は実際にp除算可能イデアルに属する。 -/
theorem deltaPDivisionRaw_base_mem_primeDividedPowerIdeal (s : σ) :
    j₀ y ∈ (E₀).primeDividedPowerIdeal :=
  ((E₀).mem_primeDividedPowerIdeal _).mpr (deltaPDivisionRaw_prime_dvd_pow D ys s)

variable [Unique σ]
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))

/-- 正則一元raw包のp除算可能イデアル上の実際の分冪構造。 -/
def deltaPDivisionRawDividedPowers : DividedPowers (E₀).primeDividedPowerIdeal :=
  (E₀).primeDividedPowers (deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy)
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map j₀)

include hpA hg hv hy hlocal in
/-- raw包の実分冪作用は、前工程の具体的な階乗分母に一致する。 -/
theorem deltaPDivisionRawDividedPowers_eq_factorialQuotient (s : σ) (n : ℕ) :
    (deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y) =
      deltaPDivisionRawFactorialQuotient D ys hlocal s n := by
  let f := deltaPDivisionToAway D a₀
  apply deltaPDivisionRawToAway_injective (σ := σ) D y hpA hg v hv hy
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  calc
    (n.factorial : Localization.Away (p : A)) * f
        ((deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y)) =
      f ((n.factorial : B₀) *
        (deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y)) := by
          rw [map_mul, map_natCast]
    _ = f ((j₀ y) ^ n) := congrArg f
      ((deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).factorial_mul_dpow_eq_pow
        (deltaPDivisionRaw_base_mem_primeDividedPowerIdeal D y s))
    _ = f ((n.factorial : B₀) * deltaPDivisionRawFactorialQuotient D ys hlocal s n) :=
      congrArg f (deltaPDivisionRawFactorialQuotient_spec D ys hlocal s n).symm
    _ = (n.factorial : Localization.Away (p : A)) *
        f (deltaPDivisionRawFactorialQuotient D ys hlocal s n) := by
          rw [map_mul, map_natCast]

end SerrePositivity.BhattScholze

end DeltaPDivisionDividedPowers

/-! ## 有限実p除算Koszul複体と通常商の正規化比較

標準包含からのH⁰単位を標準商射へ送る同型を用いる。
無限δ関係と導来δ基底変更の比較はここには含めない。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteKoszulComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 実有限関係族のspanは、既存の実有限段イデアル。 -/
theorem deltaPDivisionFiniteRelations_span (N : ℕ) :
    Ideal.span (Set.range fun i : Fin (N + 1) => g₀ i.val) = I₀ N := by
  have h := deltaPDivisionFiniteRelations_ofList (σ := σ) D y N
  have hs : {r : L₀ | r ∈ List.ofFn fun i : Fin (N + 1) => g₀ i.val} =
      Set.range (fun i : Fin (N + 1) => g₀ i.val) := by
    ext r
    simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  simpa only [Ideal.ofList, hs] using h

/-- 標準H⁰単位で正規化した、実Koszul複体のH⁰と実有限通常商の線形同型。
H⁰のこの同型自体には関係列の正則性は不要。 -/
def deltaPDivisionFiniteKoszulH0Equiv (N : ℕ) :
    (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)).homology 0 ≃ₗ[L₀]
      L₀ ⧸ I₀ N :=
  (koszulCanonicalH0Equiv L₀ (fun i : Fin (N + 1) => g₀ i.val)).trans
    (Submodule.quotEquivOfEq _ _ (deltaPDivisionFiniteRelations_span D y N))

/-- 正規化H⁰同型は実自由環の標準単位を実有限商の標準商元へ送る。 -/
theorem deltaPDivisionFiniteKoszulH0Equiv_unit (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteKoszulH0Equiv D y N
      (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
        Ideal.Quotient.mk (I₀ N) r := by
  rw [deltaPDivisionFiniteKoszulH0Equiv, LinearEquiv.trans_apply,
    koszulCanonicalH0Equiv_unit]
  exact Submodule.quotEquivOfEq_mk _ _ _ r

/-- 正規化H⁰同型を用いた、実Koszul複体から実有限通常商への添加写像。 -/
def deltaPDivisionFiniteKoszulAugmentation (N : ℕ) :
    SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N)) :=
  SerrePositivity.toSingleOfHomology _ SerrePositivity.koszulComplex_d_zero_one
    (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom

/-- 添加写像の実H⁰写像は、上で正規化した同型そのもの。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_homologyMap (N : ℕ) :
    HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulAugmentation D y N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N))).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom :=
  SerrePositivity.toSingleOfHomology_homologyMap _ _ _

/-- 実添加写像がH⁰に誘導する写像は、標準単位上で元の標準商射と一致する。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_homology_unit (N : ℕ) (r : L₀) :
    (HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulAugmentation D y N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N))).hom).hom
          (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
      Ideal.Quotient.mk (I₀ N) r := by
  rw [deltaPDivisionFiniteKoszulAugmentation_homologyMap]
  exact deltaPDivisionFiniteKoszulH0Equiv_unit D y N r

/-- 正則一元入力では、標準単位で正規化した実有限添加写像が擬同型。
これは有限の実Koszulモデルと通常商の比較である。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_quasiIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    QuasiIso (deltaPDivisionFiniteKoszulAugmentation (σ := σ) D y N) := by
  apply SerrePositivity.quasiIso_toSingleOfHomology
  exact (deltaPDivisionFiniteRelations_isKoszulResolution D y hpA hg v hv hy N).isZero

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteKoszulComparison

/-! ## 実有限p除算Koszul比較の段間自然性

末尾への関係付加は実mappingConeの包含、商側は既存の標準因子射を用いる。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteKoszulTransitions

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 次の実δ関係を末尾へ付加するKoszul複体の標準鎖写像。 -/
def deltaPDivisionFiniteKoszulTransition (N : ℕ) :
    SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val) ⟶
      SerrePositivity.koszulComplex (fun i : Fin (N + 2) => g₀ i.val) :=
  CochainComplex.mappingCone.inr
    (SerrePositivity.smulId (g₀ (N + 1))
      (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)))

/-- 実Koszul遷移射は、元の自由環からの標準H⁰単位を保存する。 -/
theorem deltaPDivisionFiniteKoszulTransition_unit (N : ℕ) (r : L₀) :
    (HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulTransition D y N) 0).hom
      (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
        koszulH0Unit L₀ (fun i : Fin (N + 2) => g₀ i.val) r := by
  exact (LinearMap.congr_fun
    (koszulH0Unit_succ L₀ (fun i : Fin (N + 2) => g₀ i.val)) r).symm

/-- 実有限通常商の標準遷移射。 -/
def deltaPDivisionFiniteQuotientTransition (N : ℕ) :
    (L₀ ⧸ I₀ N) →+* (L₀ ⧸ I₀ (N + 1)) :=
  Ideal.Quotient.factor (deltaDivisionFiniteRelationIdeal_mono D (p : A) a₀ (Nat.le_succ N))

omit [Unique σ] in
/-- 商の標準遷移射は、元の自由環の標準商元を保つ。 -/
theorem deltaPDivisionFiniteQuotientTransition_mk (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r) =
      Ideal.Quotient.mk (I₀ (N + 1)) r :=
  Ideal.Quotient.factor_mk _ r

/-- 正規化した有限H⁰同型は、実Koszul遷移射と通常商の標準遷移射を比較する。 -/
theorem deltaPDivisionFiniteKoszulH0Equiv_transition (N : ℕ)
    (z : (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)).homology 0) :
    deltaPDivisionFiniteKoszulH0Equiv D y (N + 1)
      ((HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulTransition D y N) 0).hom z) =
        deltaPDivisionFiniteQuotientTransition D y N
          (deltaPDivisionFiniteKoszulH0Equiv D y N z) := by
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective L₀ (fun i : Fin (N + 1) => g₀ i.val) z
  rw [deltaPDivisionFiniteKoszulTransition_unit, deltaPDivisionFiniteKoszulH0Equiv_unit,
    deltaPDivisionFiniteKoszulH0Equiv_unit, deltaPDivisionFiniteQuotientTransition_mk]

/-- 実有限Koszul複体を、その標準包含で繋いだ具体的な逐次図式。 -/
def deltaPDivisionFiniteKoszulDiagram :
    ℕ ⥤ CochainComplex (ModuleCat L₀) ℤ :=
  Functor.ofSequence (deltaPDivisionFiniteKoszulTransition D y)

/-- 逐次図式の隣接射は、定義した実Koszul標準遷移射。 -/
theorem deltaPDivisionFiniteKoszulDiagram_map_succ (N : ℕ) :
    (deltaPDivisionFiniteKoszulDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      deltaPDivisionFiniteKoszulTransition D y N :=
  Functor.ofSequence_map_homOfLE_succ _ N

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteKoszulTransitions

/-! ## 実有限KoszulのH⁰図式と標準有限商図式

元ごとの標準単位で正規化した比較を、共通の自由環の加群圏における自然同型にする。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteKoszulHomologyDiagram

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 通常有限商の標準遷移射を元の自由環上の線形写像として表す。 -/
def deltaPDivisionFiniteQuotientTransitionLinear (N : ℕ) :
    (L₀ ⧸ I₀ N) →ₗ[L₀] (L₀ ⧸ I₀ (N + 1)) where
  toFun := deltaPDivisionFiniteQuotientTransition D y N
  map_add' := map_add _
  map_smul' r z := by
    change deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r * z) =
      Ideal.Quotient.mk (I₀ (N + 1)) r * deltaPDivisionFiniteQuotientTransition D y N z
    rw [map_mul, deltaPDivisionFiniteQuotientTransition_mk]

omit [Unique σ] in
/-- 線形遷移写像の元上の式は、元の標準商環射。 -/
theorem deltaPDivisionFiniteQuotientTransitionLinear_apply (N : ℕ) (z : L₀ ⧸ I₀ N) :
    deltaPDivisionFiniteQuotientTransitionLinear D y N z =
      deltaPDivisionFiniteQuotientTransition D y N z := rfl

/-- 通常有限商を共通の自由環の加群として繋いだ具体的な逐次図式。 -/
def deltaPDivisionFiniteQuotientModuleDiagram : ℕ ⥤ ModuleCat L₀ :=
  Functor.ofSequence (fun N => ModuleCat.ofHom (deltaPDivisionFiniteQuotientTransitionLinear D y N))

omit [Unique σ] in
/-- 商加群図式の隣接射は、標準商遷移射の線形化。 -/
theorem deltaPDivisionFiniteQuotientModuleDiagram_map_succ (N : ℕ) :
    (deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaPDivisionFiniteQuotientTransitionLinear D y N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- 実有限Koszul図式のH⁰と標準有限商図式は、正規化された自然同型で一致する。 -/
def deltaPDivisionFiniteKoszulH0DiagramIso :
    deltaPDivisionFiniteKoszulDiagram (σ := σ) D y ⋙
        HomologicalComplex.homologyFunctor (ModuleCat L₀) (ComplexShape.up ℤ) 0 ≅
      deltaPDivisionFiniteQuotientModuleDiagram D y := by
  let η : deltaPDivisionFiniteKoszulDiagram (σ := σ) D y ⋙
        HomologicalComplex.homologyFunctor (ModuleCat L₀) (ComplexShape.up ℤ) 0 ⟶
      deltaPDivisionFiniteQuotientModuleDiagram D y :=
    NatTrans.ofSequence (fun N => (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom)
      (by
        intro N
        simp only [Functor.comp_map, deltaPDivisionFiniteKoszulDiagram_map_succ,
          deltaPDivisionFiniteQuotientModuleDiagram_map_succ]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact deltaPDivisionFiniteKoszulH0Equiv_transition D y N z)
  exact NatIso.ofComponents (fun N => (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso)
    (fun f => η.naturality f)

/-- 自然同型の各成分は、前工程の標準単位で正規化したH⁰同型。 -/
theorem deltaPDivisionFiniteKoszulH0DiagramIso_app (N : ℕ) :
    (deltaPDivisionFiniteKoszulH0DiagramIso (σ := σ) D y).hom.app N =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom := rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteKoszulHomologyDiagram

/-! ## 実一元p除算Koszul図式の逐次極限

ℤ次数の当該BS図式を転置し、既存の完全なcolim関手とホモロジー比較を使う。
原典の導来δ基底変更と同定することは、ここではまだ主張しない。
-/

@[expose] public noncomputable section DeltaPDivisionSequentialKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- BSの実有限Koszul図式を、逐次図式のℤ次数複体へ転置する。 -/
def deltaPDivisionSequentialKoszulDiagramComplex : CochainComplex (ℕ ⥤ ModuleCat.{u} L₀) ℤ where
  X i := F₀ ⋙ eval (ModuleCat.{u} L₀) (.up ℤ) i
  d i j :=
    { app := fun N => ((F₀).obj N).d i j
      naturality := fun _ _ f => ((F₀).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext N
    exact ((F₀).obj N).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext N
    exact ((F₀).obj N).d_comp_d i j k

/-- BSの当該転置複体のホモロジーは、実各段ホモロジーの図式。 -/
def deltaPDivisionSequentialKoszulDiagramHomologyIso (i : ℤ) :
    (deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y).homology i ≅
      F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i := by
  let K := deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y
  refine NatIso.ofComponents (fun N => ((K.sc i).mapHomologyIso
    ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).symm) ?_
  intro N M f
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i)
    ((evaluation ℕ (ModuleCat.{u} L₀)).map f)
  change homologyMap ((F₀).map f) i =
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
      (K.homology i).map f ≫
      ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj M)).inv at h
  apply (cancel_epi ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map] using h.symm

/-- 完全な逐次colim関手を用いて各項で作る、実BS図式の極限複体。 -/
def deltaPDivisionSequentialKoszulTermwiseColimit : CochainComplex (ModuleCat.{u} L₀) ℤ :=
  ((colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapHomologicalComplex (.up ℤ)).obj
    (deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y)

/-- 各項で作った実極限は、元の実Koszul図式の圏論的colimitである。 -/
def deltaPDivisionSequentialKoszulTermwiseColimitIso :
    deltaPDivisionSequentialKoszulTermwiseColimit (σ := σ) D y ≅ colimit F₀ :=
  IsColimit.coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F₀) (colimit.isColimit F₀)

/-- 当該BS図式の実圏論的colimitのホモロジーは、各段ホモロジーのcolimit。 -/
def deltaPDivisionSequentialKoszulHomologyColimitIso (i : ℤ) :
    (colimit F₀).homology i ≅ colimit (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i) :=
by
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} L₀) := AB5OfSize_of_univLE (ModuleCat.{u} L₀)
  exact
    (homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i).mapIso
      (deltaPDivisionSequentialKoszulTermwiseColimitIso (σ := σ) D y).symm ≪≫
    ((deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y).sc i).mapHomologyIso
      (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀) ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapIso
      (deltaPDivisionSequentialKoszulDiagramHomologyIso (σ := σ) D y i)
/-- 実逐次Koszul極限のH⁰は、標準有限商加群図式のcolimitに一致する。 -/
def deltaPDivisionSequentialKoszulH0ColimitIso :
    (colimit F₀).homology 0 ≅ colimit (deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y) :=
  deltaPDivisionSequentialKoszulHomologyColimitIso (σ := σ) D y 0 ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapIso
      (deltaPDivisionFiniteKoszulH0DiagramIso (σ := σ) D y)

/-- 正則一元入力では、実逐次Koszul極限は零以外の全次数でホモロジーが零。
無限δ基底変更との同定を仮定して得た結論ではない。 -/
theorem deltaPDivisionSequentialKoszul_isZero_homology
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((colimit F₀).homology i) := by
  have hz : IsZero (colimit (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    exact (deltaPDivisionFiniteRelations_isKoszulResolution D y hpA hg v hv hy N).isZero i hi
      |>.eq_of_src _ _
  exact hz.of_iso (deltaPDivisionSequentialKoszulHomologyColimitIso (σ := σ) D y i)

end SerrePositivity.BhattScholze

end DeltaPDivisionSequentialKoszul

/-! ## 通常有限関係商の逐次極限としてのraw δ包

実δ閉包が有限関係イデアルの上限である既存定理を使う。
実標準商射で与えられる余錐の普遍性を、共通の自由環の加群圏で証明する。
-/

@[expose] public noncomputable section DeltaPDivisionFiniteQuotientColimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀
local notation "J₀" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal (p : A) a₀)
local notation "Q₀" => deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y

omit [Unique σ] in
private theorem finite_le_raw (N : ℕ) : I₀ N ≤ J₀ := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  exact le_iSup _ N

/-- 有限通常商からraw δ包への標準L線形射。 -/
def deltaPDivisionFiniteQuotientToRaw (N : ℕ) :
    (L₀ ⧸ I₀ N) →ₗ[L₀] DeltaAdjoinDivision D (p : A) a₀ :=
  Submodule.mapQ (I₀ N) J₀ LinearMap.id (by exact finite_le_raw D y N)

omit [Unique σ] in
/-- raw δ包への射は元の自由環の標準商元を保つ。 -/
theorem deltaPDivisionFiniteQuotientToRaw_mk (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r) =
      Ideal.Quotient.mk J₀ r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限商図式からraw δ包への標準余錐。 -/
def deltaPDivisionFiniteQuotientRawCocone : Cocone Q₀ where
  pt := ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀)
  ι := NatTrans.ofSequence (fun N => ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N))
    (by
      intro N
      rw [deltaPDivisionFiniteQuotientModuleDiagram_map_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change deltaPDivisionFiniteQuotientToRaw D y (N + 1)
        (deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r)) =
        deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r)
      rw [deltaPDivisionFiniteQuotientTransition_mk,
        deltaPDivisionFiniteQuotientToRaw_mk, deltaPDivisionFiniteQuotientToRaw_mk])

omit [Unique σ] in
private theorem cocone_mk_independent (c : Cocone Q₀) (N : ℕ) (r : L₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (I₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (I₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (I₀ N) r))
        (c.w (homOfLE (Nat.le_succ N)))
      rw [deltaPDivisionFiniteQuotientModuleDiagram_map_succ] at h
      change (c.ι.app (N + 1)).hom
        (deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r)) = _ at h
      rw [deltaPDivisionFiniteQuotientTransition_mk] at h
      exact h.trans ih

omit [Unique σ] in
private theorem cocone_base_ker (c : Cocone Q₀) :
    J₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0))) := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (I₀ 0) r) = 0
  rw [← cocone_mk_independent D y c N r,
    Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- raw δ包の標準余錐は、実通常有限商図式のcolimitである。 -/
def deltaPDivisionFiniteQuotientRawIsColimit :
    IsColimit (deltaPDivisionFiniteQuotientRawCocone (σ := σ) D y) where
  desc c := ModuleCat.ofHom
    (Submodule.liftQ J₀ ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0)))
      (by exact cocone_base_ker D y c))
  fac c N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Submodule.liftQ J₀ ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0)))
      (cocone_base_ker D y c)
      (deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r)) = _
    rw [deltaPDivisionFiniteQuotientToRaw_mk]
    exact (cocone_mk_independent D y c N r).symm
  uniq c f hf := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (I₀ 0) r)) (hf 0)
    change f.hom (deltaPDivisionFiniteQuotientToRaw D y 0 (Ideal.Quotient.mk (I₀ 0) r)) = _ at h
    rw [deltaPDivisionFiniteQuotientToRaw_mk] at h
    exact h

/-- 実有限通常商の圏論的colimitとraw δ包の標準比較同型。 -/
def deltaPDivisionFiniteQuotientColimitRawIso :
    colimit Q₀ ≅ ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀) :=
  (colimit.isColimit Q₀).coconePointUniqueUpToIso (deltaPDivisionFiniteQuotientRawIsColimit D y)

omit [Unique σ] in
/-- 標準比較同型は、各有限通常商のraw δ包への標準射と一致する。 -/
theorem deltaPDivisionFiniteQuotientColimitRawIso_ι (N : ℕ) :
    colimit.ι Q₀ N ≫ (deltaPDivisionFiniteQuotientColimitRawIso D y).hom =
      ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Q₀)
    (deltaPDivisionFiniteQuotientRawIsColimit D y) N

/-- 実無限KoszulモデルのH⁰は、raw δ包にL線形同型となる。 -/
def deltaPDivisionSequentialKoszulH0RawIso :
    (colimit (deltaPDivisionFiniteKoszulDiagram (σ := σ) D y)).homology 0 ≅
      ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀) :=
  deltaPDivisionSequentialKoszulH0ColimitIso D y ≪≫ deltaPDivisionFiniteQuotientColimitRawIso D y

end SerrePositivity.BhattScholze

end DeltaPDivisionFiniteQuotientColimit

/-! ## raw δ p除算包の元のA上の実mod p・導来完備化比較 -/

@[expose] public noncomputable section DeltaPDivisionRawRelativeModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 正則一元raw包には、元のA→A/pへの実係数拡大で高次Torが生じない。 -/
theorem deltaPDivisionRawRelativeModP_torVanishing
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    scalarExtensionTorVanishing q₀ (ModuleCat.of A B₀) := by
  intro n hn
  let e := (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso
  have hz := principalDPRelativeModP_torVanishing y hA hpA hy n hn
  exact IsZero.of_iso hz
    (((Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule q₀)).mapIso e)

/-- 元のA→A/pへのraw包の実導来還元を、具体的な分冪表示環へ同定する。 -/
def deltaPDivisionRawRelativeDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso
        (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 元のA上のraw包の実導来完備化も、実p還元後は具体的な表示環となる。 -/
def deltaPDivisionRawRelativeCompletedDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- raw包の実mod p比較は、元のA上の標準導来完備化単位と両立する。 -/
theorem deltaPDivisionRawRelativeCompletedDerivedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀))) ≫
      (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy).hom =
        (deltaPDivisionRawRelativeDerivedModPIso D y hA hpA hg v hv hy).hom := by
  let e := boundedAboveDerivedSingleFunctor.mapIso
    (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionRawRelativeModP

/-! ## raw包の実導来完備化のp還元ホモロジーと相対平坦性 -/

@[expose] public noncomputable section DeltaPDivisionRawResidueFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ D.frobeniusLift y)
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 元のA上のraw包の実完備化をp還元した実H0は、具体的表示環とA/p線形同値。 -/
def deltaPDivisionRawCompletedModPH0Equiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
      (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)) ≃ₗ[Q₀]
      PrincipalDPPresentation Q₀ (q₀ y) := by
  let e := DerivedCategory.Minus.ι.mapIso
    (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Q₀) 0).app
      (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y)))).toLinearEquiv

/-- この実p還元の全非零次数ホモロジーは零。 -/
theorem deltaPDivisionRawCompletedModP_homology_isZero
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) i).obj
      (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy))
  exact IsZero.of_iso
    (derivedSingleHomology_isZero (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) i hi) e

/-- 任意のK→A/p作用に対し、p乗商のK平坦性から実完備化のp還元H0のK平坦性を得る。 -/
theorem deltaPDivisionRawCompletedModPH0_flat_of_powerQuotient_flat
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    {K : Type v} [CommRing K] [Algebra K Q₀]
    (hQ : Module.Flat K (Q₀ ⧸ Ideal.span {(q₀ y) ^ p})) :
    Module.Flat K ((ModuleCat.restrictScalars (algebraMap K Q₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
        (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj))) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
    (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)
  let : Module K M := Module.compHom M (algebraMap K Q₀)
  let : IsScalarTower K Q₀ M := IsScalarTower.of_compHom K Q₀ M
  have hpQ : (p : Q₀) = 0 := by
    change Ideal.Quotient.mk _ (p : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let := principalDPPresentation_flat_of_quotient_flat
    (A := K) (Fact.out : p.Prime) hpQ (q₀ y) hQ
  exact Module.Flat.of_linearEquiv
    ((deltaPDivisionRawCompletedModPH0Equiv D y hA hpA hg v hv hy).restrictScalars K)

end SerrePositivity.BhattScholze

end DeltaPDivisionRawResidueFlat

/-! ## 正則な一元p除算の実導来完備化からの通常剰余射

元の係数射がp,yを消す場合を扱う。raw包のp正則性の仮定を明示して
旧ねじれ除去商を経由し、実H⁰から環として延長する。
一般の導来Koszul代数への射・CFF・prism性は結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionResidueMap

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
attribute [local instance] derivedDeltaDivisionCommRing
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "R₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "H₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "j₀" => deltaDivisionTorsionMap D (p : A) a₀
local notation "u₀" => pdCompletionUnit R₀ p (j₀ (p : A))
local notation "k₀" => derivedDeltaDivisionMap D (p : A) a₀

section General
variable {B : Type u} [CommRing B] (q : A →+* B) (hqy : q y = 0)

/-- raw/旧ねじれ除去商同型を使って、具体的通常評価を既存商へ因子化する。 -/
def deltaPDivisionTorsionResidueMap : R₀ →+* B :=
  (deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy)).comp
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hgL v hv hy).symm.toRingHom

/-- 因子化は実際の旧ねじれ除去標準商射と両立する。 -/
theorem deltaPDivisionTorsionResidueMap_comp_raw :
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp
      (Ideal.Quotient.mk ((deltaAdjoinDivisionStructure D (p : A) a₀).deltaClosure
        (RingHom.ker (algebraMap B₀ (Localization.Away
          (deltaAdjoinDivisionMap D (p : A) a₀ (p : A))))))) =
      deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy) := by
  let e := deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hgL v hv hy
  apply RingHom.ext
  intro b
  change deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy)
    (e.symm (Ideal.Quotient.mk _ b)) = _
  have he : e b = Ideal.Quotient.mk _ b :=
    deltaPDivisionRawTorsionEquiv_apply (σ := σ) D y hpA hgL v hv hy b
  rw [← he, RingEquiv.symm_apply_apply]

/-- 旧ねじれ除去商からの通常剰余射は、元の係数射qを保つ。 -/
theorem deltaPDivisionTorsionResidueMap_comp_base :
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp j₀ = q := by
  change (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp
    ((Ideal.Quotient.mk _).comp (deltaAdjoinDivisionMap D (p : A) a₀)) = q
  rw [← RingHom.comp_assoc, deltaPDivisionTorsionResidueMap_comp_raw,
    deltaPDivisionWittResidueMap_comp_base]

private theorem complete_of_zero_scalar (b : B) (hb : b = 0) :
    IsModuleComplete B b (ModuleCat.of B B) := by
  apply isModuleComplete_of_pow_smul_zero B b (ModuleCat.of B B) 1
  intro x
  rw [pow_one, hb, zero_smul]

variable (hqp : q (p : A) = 0)
include hqp

/-- p,yを消す係数射への通常剰余射は、実導来完備化H⁰から一意に延長する。 -/
theorem existsUnique_deltaPDivisionDerivedResidueMap :
    ∃! f : H₀ →+* B, f.comp u₀ =
      deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy := by
  have hpB : (p : B) = 0 := (map_natCast q p).symm.trans hqp
  have hdB : deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy
      (j₀ (p : A)) = 0 :=
    (RingHom.congr_fun (deltaPDivisionTorsionResidueMap_comp_base D y hpA hgA hgL v hv hy q hqy)
      (p : A)).trans hqp
  exact existsUnique_pdCompletionRingHom R₀ p (j₀ (p : A)) B
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy)
    (complete_of_zero_scalar (p : B) hpB) (complete_of_zero_scalar _ hdB)

/-- 実導来完備化H⁰から、p,yを消す具体的係数射の終域への通常環射。 -/
def deltaPDivisionDerivedResidueMap : H₀ →+* B :=
  (existsUnique_deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).choose

/-- 実H⁰からの射は旧ねじれ除去商の実Koszul標準単位と両立する。 -/
theorem deltaPDivisionDerivedResidueMap_comp_unit :
    (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp u₀ =
      deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy :=
  (existsUnique_deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).choose_spec.1

/-- 実H⁰からの射と元のAからの標準射の合成はq。 -/
theorem deltaPDivisionDerivedResidueMap_comp_base :
    (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp k₀ = q := by
  change (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp
    ((u₀).comp j₀) = q
  rw [← RingHom.comp_assoc, deltaPDivisionDerivedResidueMap_comp_unit,
    deltaPDivisionTorsionResidueMap_comp_base]

/-- 元の係数射が全射なら、この具体的通常剰余射も全射。 -/
theorem deltaPDivisionDerivedResidueMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp) := by
  intro b
  obtain ⟨r, hr⟩ := hq b
  exact ⟨k₀ r, (RingHom.congr_fun
    (deltaPDivisionDerivedResidueMap_comp_base D y hpA hgA hgL v hv hy q hqy hqp) r).trans hr⟩
end General

/-- 実導来完備化からA/(p,y)への具体的通常環射。 -/
def deltaPDivisionDerivedResidueQuotientMap : H₀ →+* (A ⧸ Ideal.span {(p : A), y}) :=
  deltaPDivisionDerivedResidueMap (σ := σ) D y hpA hgA hgL v hv hy
    (Ideal.Quotient.mk (Ideal.span {(p : A), y}))
    (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)))

/-- 具体的剰余射はAからの標準商写像を延長する。 -/
theorem deltaPDivisionDerivedResidueQuotientMap_comp_base :
    (deltaPDivisionDerivedResidueQuotientMap (σ := σ) D y hpA hgA hgL v hv hy).comp k₀ =
      Ideal.Quotient.mk (Ideal.span {(p : A), y}) :=
  deltaPDivisionDerivedResidueMap_comp_base D y hpA hgA hgL v hv hy _ _ _

/-- 実H⁰からA/(p,y)への具体的通常剰余射は全射。 -/
theorem deltaPDivisionDerivedResidueQuotientMap_surjective :
    Function.Surjective
      (deltaPDivisionDerivedResidueQuotientMap (σ := σ) D y hpA hgA hgL v hv hy) :=
  deltaPDivisionDerivedResidueMap_surjective D y hpA hgA hgL v hv hy _ _ _
    Ideal.Quotient.mk_surjective

end SerrePositivity.BhattScholze

end DeltaPDivisionResidueMap

/-! ## raw δ包への実無限Koszul添加写像

実有限Koszul図式の圏論的colimitを用い、その実H⁰からraw δ包へ写す。
原典の導来δpushout・導来完備化・CFFとの比較とは区別する。
-/

@[expose] public noncomputable section DeltaPDivisionSequentialKoszulAugmentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- 実Koszul逐次極限の正次数の項は零。関係列の正則性は不要。 -/
theorem deltaPDivisionSequentialKoszul_isZero_X (i : ℤ) (hi : 0 < i) :
    IsZero ((colimit F₀).X i) := by
  have hz : IsZero (colimit (F₀ ⋙ eval (ModuleCat.{u} L₀) (.up ℤ) i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    exact (SerrePositivity.koszulComplex_isZero_X_of_pos
      (fun j : Fin (N + 1) => g₀ j.val) i hi).eq_of_src _ _
  exact hz.of_iso (preservesColimitIso (eval (ModuleCat.{u} L₀) (.up ℤ) i) F₀)

/-- 実Koszul逐次極限の零次から一次への微分は零。 -/
theorem deltaPDivisionSequentialKoszul_d_zero_one :
    (colimit F₀).d 0 1 = 0 :=
  (deltaPDivisionSequentialKoszul_isZero_X D y 1 (by decide)).eq_of_tgt _ _

/-- raw δ包への実無限Koszul添加写像。H⁰に実raw比較同型を用いる。 -/
def deltaPDivisionSequentialKoszulAugmentation :
    colimit F₀ ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀)) :=
  SerrePositivity.toSingleOfHomology _ (deltaPDivisionSequentialKoszul_d_zero_one D y)
    (deltaPDivisionSequentialKoszulH0RawIso D y).hom

/-- 添加写像のH⁰は、実極限比較により得たraw δ包との同型。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_homologyMap :
    homologyMap (deltaPDivisionSequentialKoszulAugmentation (σ := σ) D y) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀))).hom =
      (deltaPDivisionSequentialKoszulH0RawIso D y).hom :=
  SerrePositivity.toSingleOfHomology_homologyMap _ _ _

/-- 正則一元入力では、raw δ包への実無限Koszul添加写像は擬同型。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_quasiIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    QuasiIso (deltaPDivisionSequentialKoszulAugmentation (σ := σ) D y) := by
  apply SerrePositivity.quasiIso_toSingleOfHomology
  exact deltaPDivisionSequentialKoszul_isZero_homology D y hpA hg v hv hy

end SerrePositivity.BhattScholze

end DeltaPDivisionSequentialKoszulAugmentation

/-! ## 実無限Koszul比較の標準単位

圏論的colimitへの標準射を追い、H⁰比較を元の自由環の標準商射で正規化する。
-/

@[expose] public noncomputable section DeltaPDivisionSequentialKoszulUnit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- 実ホモロジー極限比較は、各有限Koszul段からの実標準射を保つ。 -/
theorem deltaPDivisionSequentialKoszulHomologyColimitIso_ι (i : ℤ) (N : ℕ) :
    homologyMap (colimit.ι F₀ N) i ≫
      (deltaPDivisionSequentialKoszulHomologyColimitIso D y i).hom =
        colimit.ι (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i) N := by
  haveI : AB5OfSize.{0, 0} (ModuleCat.{u} L₀) := AB5OfSize_of_univLE (ModuleCat.{u} L₀)
  let K := deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y
  let τ : (evaluation ℕ (ModuleCat.{u} L₀)).obj N ⟶
      (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀) :=
    { app := fun U => colimit.ι U N
      naturality := fun U V f => (colimit.ι_map f N).symm }
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i) τ
  change homologyMap ((coconeOfHasColimitEval F₀).ι.app N) i =
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
      colimit.ι (K.homology i) N ≫
      ((K.sc i).mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀)).inv at h
  dsimp only [K] at h
  have hc : colimit.ι F₀ N ≫
      (deltaPDivisionSequentialKoszulTermwiseColimitIso D y).inv =
        (coconeOfHasColimitEval F₀).ι.app N :=
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitCoconeOfHasColimitEval F₀) (colimit.isColimit F₀) N
  simp only [deltaPDivisionSequentialKoszulHomologyColimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, homologyFunctor_map]
  rw [← homologyMap_comp_assoc, hc, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [colimit.ι_map]
  change ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc]

/-- 実H⁰極限比較は、通常有限商の標準遷移図式への比較とも両立する。 -/
theorem deltaPDivisionSequentialKoszulH0ColimitIso_ι (N : ℕ) :
    homologyMap (colimit.ι F₀ N) 0 ≫ (deltaPDivisionSequentialKoszulH0ColimitIso D y).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom ≫
        colimit.ι (deltaPDivisionFiniteQuotientModuleDiagram D y) N := by
  rw [deltaPDivisionSequentialKoszulH0ColimitIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, deltaPDivisionSequentialKoszulHomologyColimitIso_ι,
    colimit.ι_map, deltaPDivisionFiniteKoszulH0DiagramIso_app]

/-- 実H⁰とraw δ包の比較は、有限段の実H⁰比較とraw標準射を保つ。 -/
theorem deltaPDivisionSequentialKoszulH0RawIso_ι (N : ℕ) :
    homologyMap (colimit.ι F₀ N) 0 ≫ (deltaPDivisionSequentialKoszulH0RawIso D y).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom ≫
        ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N) := by
  rw [deltaPDivisionSequentialKoszulH0RawIso, Iso.trans_hom, ← Category.assoc,
    deltaPDivisionSequentialKoszulH0ColimitIso_ι, Category.assoc,
    deltaPDivisionFiniteQuotientColimitRawIso_ι]

/-- 任意有限段の標準単位を実極限へ送ると、raw比較は元の標準商元を与える。 -/
theorem deltaPDivisionSequentialKoszulH0RawIso_unit (N : ℕ) (r : L₀) :
    (deltaPDivisionSequentialKoszulH0RawIso D y).hom.hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀)) r := by
  have h := congrArg (fun f => f.hom (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
    (fun j : Fin (N + 1) => g₀ j.val) r)) (deltaPDivisionSequentialKoszulH0RawIso_ι D y N)
  change (deltaPDivisionSequentialKoszulH0RawIso D y).hom.hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
    deltaPDivisionFiniteQuotientToRaw D y N
      (deltaPDivisionFiniteKoszulH0Equiv D y N
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) at h
  rw [deltaPDivisionFiniteKoszulH0Equiv_unit, deltaPDivisionFiniteQuotientToRaw_mk] at h
  exact h

/-- 実無限添加写像のH⁰も、各有限段の標準単位をraw標準商元へ送る。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_homology_unit (N : ℕ) (r : L₀) :
    (homologyMap (deltaPDivisionSequentialKoszulAugmentation D y) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀))).hom).hom
      ((homologyMap (colimit.ι F₀ N) 0).hom
        (SerrePositivity.DerivedCompletion.koszulH0Unit L₀
          (fun j : Fin (N + 1) => g₀ j.val) r)) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀)) r := by
  rw [deltaPDivisionSequentialKoszulAugmentation_homologyMap]
  exact deltaPDivisionSequentialKoszulH0RawIso_unit D y N r

end SerrePositivity.BhattScholze

end DeltaPDivisionSequentialKoszulUnit
