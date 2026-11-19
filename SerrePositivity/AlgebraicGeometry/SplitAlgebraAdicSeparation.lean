module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientMembership
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
概要：KST §5、Stacks 05DH・05FS の準備となる分裂代数のイデアル冪に関する分離性。
方針：拡大イデアルの所属を各係数へ移し、基礎環の分離性を使う。
規約：分裂は実際の線形写像で与え、基礎環上有限とは仮定しない。
使われ方：特別な局所化と完備化の単射性を検証する既存経路の準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {ι : Type*}
  (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
  (hpe : p.comp e = LinearMap.id)

include e p hpe

/--
概要：基礎環が分離的なら全ての拡大イデアル冪に属する元は零。
方針：各係数が全ての基礎イデアル冪に属することを使い、分裂で元へ戻す。
規約：KST §5、Stacks 05DH, Lemma 38.7.4・05FS, Lemma 38.9.2 の準備。
使われ方：代数上のイデアル冪の共通部分と完備化への単射性。
-/
theorem splitAlgebra_eq_zero_of_mem_map_powers (I : Ideal A) [IsHausdorff I A]
    (x : B) (hx : ∀ n : ℕ, x ∈ (I ^ n).map (algebraMap A B)) : x = 0 := by
  have he : e x = 0 := by
    ext i
    apply IsHausdorff.haus' (I := I)
    intro n
    apply SModEq.zero.mpr
    rw [Ideal.smul_top_eq_map]
    change e x i ∈ (I ^ n).map (algebraMap A A)
    simpa only [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id] using
      (splitAlgebra_mem_map_iff e p hpe (I ^ n) x).mp (hx n) i
  have hp := LinearMap.congr_fun hpe x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, he, map_zero] using hp.symm

/--
概要：基礎環がイデアル冪について分離的なら分裂代数も基礎環加群として分離的。
方針：イデアルによる部分加群の積を拡大イデアルへ同定する。
規約：KST §5、Stacks 05DH・05FS の準備、代数上有限生成とは仮定しない。
使われ方：拡大イデアルの完備化への写像の単射性。
-/
theorem splitAlgebra_isHausdorff (I : Ideal A) [IsHausdorff I A] : IsHausdorff I B := by
  refine ⟨fun x hx => splitAlgebra_eq_zero_of_mem_map_powers e p hpe I x ?_⟩
  intro n
  have hn := SModEq.zero.mp (hx n)
  rw [Ideal.smul_top_eq_map] at hn
  exact hn

/--
概要：分裂代数は拡大イデアルの冪についても分離的。
方針：基礎環加群としての分離性を拡大イデアルによる分離性へ移す。
規約：KST §5、Stacks 05DH・05FS の準備、基礎環の分離性を仮定する。
使われ方：代数自身のイデアルに関する完備化を扱う。
-/
theorem splitAlgebra_isHausdorff_map (I : Ideal A) [IsHausdorff I A] :
    IsHausdorff (I.map (algebraMap A B)) B := by
  let : IsHausdorff I B := splitAlgebra_isHausdorff e p hpe I
  exact IsHausdorff.map_algebraMap_iff.mpr inferInstance

/--
概要：分裂代数から拡大イデアルの完備化への実際の写像は単射。
方針：分離性と完備化の標準写像の単射性判定を使う。
規約：KST §5、Stacks 05DH・05FS の準備、完備化の平坦性は主張しない。
使われ方：局所環上の代数を完備化へ埋め込む。
-/
theorem splitAlgebra_adicCompletion_injective (I : Ideal A) [IsHausdorff I A] :
    Function.Injective (AdicCompletion.of (I.map (algebraMap A B)) B) := by
  let : IsHausdorff (I.map (algebraMap A B)) B := splitAlgebra_isHausdorff_map e p hpe I
  exact AdicCompletion.of_injective _ _

/--
概要：Noether 局所環上の分裂代数は極大イデアルの拡大について分離的。
方針：基礎環に対する Krull の共通部分定理を各係数に適用する。
規約：KST §5、Stacks 05DH・05FS の準備、有限性は基礎環の Noether 性に課す。
使われ方：閉ファイバーを用いた特別な局所化と完備化の比較。
-/
theorem splitAlgebra_isHausdorff_maximalIdeal [IsNoetherianRing A] [IsLocalRing A] :
    IsHausdorff ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B :=
  splitAlgebra_isHausdorff_map e p hpe (IsLocalRing.maximalIdeal A)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
