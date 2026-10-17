module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers

/-!
# BS Rem 7.15（著者版 p.62）：p と ϖ の完全平坦性の照合

## 概要
主イデアル (ϖ^n)=(c) の下で c 完全平坦性と ϖ 完全平坦性を比較する。
通常の商による逆向きの判定には、基底と加群上の ϖ 正則性を明示する。

## 方針
冪ねじれ加群の Tor 消滅と忠実性の既存 API を用いる。

## 規約
任意の可換環で成り立つ形を公開する。原典では c=p、n=p、ϖ^p=p·単元を用いる。
通常商の平坦性だけから高次 Tor 消滅を推論しない。

## 使われ方
R/ϖ の pd 計算と候補の p 完全忠実平坦性を結ぶ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open TensorProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

/-- 概要：ϖ の正冪が c と単元の積なら、同じ主イデアルを生成する。
方針：単元倍で主イデアルが不変であることを使う。
規約：任意の環と指数に成立する。
使われ方：BS Rem 7.15（著者版 p.62）の ϖ^p=u·p から一般比較への入力。 -/
theorem span_power_eq_of_unit (v c : R) (n : ℕ) (u : Rˣ)
    (hpow : v ^ n = (u : R) * c) : Ideal.span {v ^ n} = Ideal.span {c} := by
  rw [hpow, mul_comm]
  exact Ideal.span_singleton_mul_right_unit u.isUnit c

/-- 概要：試験イデアルを大きくすると完全平坦性は保存される。
方針：消滅条件を包含で制限する。規約：正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の p から ϖ への方向。 -/
theorem completelyFlat_of_le (I J : Ideal R) (hIJ : I ≤ J)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M) :
    IsCompletelyFlat J M := by
  intro N _ _ hN
  exact hM N (fun r hr => hN r (hIJ hr))

/-- 概要：同じ主イデアルを生成する正冪は完全平坦性を変えない。
方針：試験イデアルの包含と既存の有限冪デヴィサージュを使う。
規約：基底・加群の正則性も完備性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の (ϖ^p)=(p)。 -/
theorem completelyFlat_iff (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFlat (Ideal.span {c}) M ↔ IsCompletelyFlat (Ideal.span {v}) M := by
  constructor
  · intro hM
    apply completelyFlat_of_le _ _ ?_ M hM
    rw [← hspan]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self v (Nat.ne_of_gt hn))
  · intro hM
    simpa only [hspan] using isCompletelyFlat_principal_power v M hM n

/-- 概要：c 完全忠実平坦な加群の通常の ϖ 還元は忠実平坦。
方針：c で消える試験加群の零性検出を ϖ 剰余テンソルへ移す。
規約：(ϖ^n)=(c)、n>0 のみを要し、加群の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の原典の通常忠実平坦性。 -/
theorem residueTensor_faithfullyFlat (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {c}) M) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {v}) ((R ⧸ Ideal.span {v}) ⊗[R] M) := by
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality _ _).mpr
  refine ⟨flat_residueTensor_of_completelyFlat _ M
    ((completelyFlat_iff v c n hn hspan M).mp hM.1), ?_⟩
  intro N _ _ hTensor
  let I := Ideal.span {v}
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  let _ : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) := hTensor
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N M
  have hTN : Subsingleton (N ⊗[R] M) := e.surjective.subsingleton
  have hc : c ∈ I := by
    have hle : Ideal.span {c} ≤ I := by
      rw [← hspan]
      exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self v (Nat.ne_of_gt hn))
    exact hle (Ideal.mem_span_singleton_self _)
  have hN : ∀ x : N, c ^ 1 • x = 0 := by
    intro x
    change Ideal.Quotient.mk I (c ^ 1) • x = 0
    rw [pow_one, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_smul]
  have := hM.2
  exact subsingleton_of_power_torsion_of_residueTensor c M 1 N hN hTN

/-- 概要：同じ主イデアルを生成する正冪は完全忠実平坦性を変えない。
方針：ϖ 還元の忠実性と各正冪の忠実性を既存 API から得る。
規約：任意の加群に成立し、正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の p と ϖ の係数表記の照合。 -/
theorem completelyFaithfullyFlat_iff (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (M : Type u) [AddCommGroup M] [Module R M] :
    IsCompletelyFaithfullyFlat (Ideal.span {c}) M ↔
      IsCompletelyFaithfullyFlat (Ideal.span {v}) M := by
  constructor
  · intro hM
    exact ⟨(completelyFlat_iff v c n hn hspan M).mp hM.1,
      residueTensor_faithfullyFlat v c n hn hspan M hM⟩
  · intro hM
    refine ⟨(completelyFlat_iff v c n hn hspan M).mpr hM.1, ?_⟩
    rw [← hspan]
    exact faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat v M hM n

/-- 概要：基底と M 上で ϖ が正則なら、c 完全平坦性は通常商の平坦性と同値。
方針：主元の正則性判定と冪による完全平坦性の不変性を組み合わせる。
規約：M 上の正則性を落とすと M=R/(ϖ) が反例となる。
使われ方：BS Rem 7.15（著者版 p.62）の pd 計算による判定。 -/
theorem completelyFlat_iff_flat_reduction (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c}) (hv : IsSMulRegular R v)
    (M : Type u) [AddCommGroup M] [Module R M] (hMv : IsSMulRegular M v) :
    IsCompletelyFlat (Ideal.span {c}) M ↔
      Module.Flat (R ⧸ Ideal.span {v}) (AdicReduction (Ideal.span {v}) M) := by
  rw [completelyFlat_iff v c n hn hspan M]
  constructor
  · intro hM
    have := flat_residueTensor_of_completelyFlat _ M hM
    exact Module.Flat.of_linearEquiv (quotientTensorReductionEquiv (Ideal.span {v}) M).symm
  · intro hM
    have := hM
    exact isCompletelyFlat_principal_of_regular v hv M hMv
      (Module.Flat.of_linearEquiv (quotientTensorReductionEquiv (Ideal.span {v}) M))

/-- 概要：基底と M 上で ϖ が正則なら、c 完全忠実平坦性は通常商の忠実平坦性と同値。
方針：正則主元の忠実平坦判定を完全忠実平坦性の冪不変性で移す。
規約：通常商と導来商を正則性なしに同一視しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典の忠実平坦性の説明。 -/
theorem completelyFaithfullyFlat_iff_faithfullyFlat_reduction
    (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c}) (hv : IsSMulRegular R v)
    (M : Type u) [AddCommGroup M] [Module R M] (hMv : IsSMulRegular M v) :
    IsCompletelyFaithfullyFlat (Ideal.span {c}) M ↔
      Module.FaithfullyFlat (R ⧸ Ideal.span {v}) (AdicReduction (Ideal.span {v}) M) := by
  rw [completelyFaithfullyFlat_iff v c n hn hspan M]
  constructor
  · intro hM
    have := hM.2
    exact Module.FaithfullyFlat.of_linearEquiv _ _
      (quotientTensorReductionEquiv (Ideal.span {v}) M).symm
  · intro hM
    have := hM
    exact isCompletelyFaithfullyFlat_principal_of_regular v hv M hMv
      (Module.FaithfullyFlat.of_linearEquiv _ _ (quotientTensorReductionEquiv (Ideal.span {v}) M))

attribute [local instance] adicQuotientAlgebra

/-- 概要：c 完全忠実平坦な R 代数の ϖ 商は R/ϖ 上忠実平坦。
方針：通常剰余テンソルと像イデアル商の標準同型を使う。
規約：代数の正則性を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の候補 T の通常剰余。 -/
theorem algebraQuotient_faithfullyFlat (v c : R) (n : ℕ) (hn : 0 < n)
    (hspan : Ideal.span {v ^ n} = Ideal.span {c})
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsCompletelyFaithfullyFlat (Ideal.span {c}) T) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {v})
      (T ⧸ (Ideal.span {v}).map (algebraMap R T)) := by
  have := residueTensor_faithfullyFlat v c n hn hspan T hT
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.VarpiComparison
