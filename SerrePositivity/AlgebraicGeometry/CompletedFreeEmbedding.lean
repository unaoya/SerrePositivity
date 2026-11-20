module

public import SerrePositivity.AlgebraicGeometry.CompletedFinsuppCoordinates

/-!
概要：KST §5、Stacks 05BC・05DJ の自由加群の完備化から係数環の積への実際の埋め込み。
方針：完備化した各座標を、基礎環の完備性の線形同型で元の係数へ戻す。
規約：このファイルの単射性には Noether 性は不要、普遍単射性は別に証明する。
使われ方：係数環の積の Mittag–Leffler 性を自由加群の完備化へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：自由加群のイデアル進完備化から完備な基礎環の任意の積への実際の線形写像。
方針：完備化座標写像と、各係数での標準完備化の逆同型を合成する。
規約：KST §5、Stacks 05BC, Lemma 15.28.1、自由加群は有限台関数として固定する。
使われ方：自由加群の完備化の普遍単射な積埋め込みを構成する。
-/
def completedFreeEmbedding {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (A : Type*) : AdicCompletion I (A →₀ R) →ₗ[R] (A → R) :=
  (LinearEquiv.piCongrRight (fun _ : A => (AdicCompletion.ofLinearEquiv I R).symm)).toLinearMap.comp
    (completedFinsuppCoordinates I A R)

/--
概要：自由加群の完備化の埋め込みの各成分は、完備化した座標の基礎環での値。
方針：積上の線形同型と完備化座標の定義を使う。
規約：KST §5、Stacks 05BC、基礎環の完備性の実際の逆同型を明示する。
使われ方：テンソルと完備化の比較の成分の計算。
-/
theorem completedFreeEmbedding_apply {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (A : Type*) (x : AdicCompletion I (A →₀ R)) (a : A) :
    completedFreeEmbedding I A x a = (AdicCompletion.ofLinearEquiv I R).symm
      (AdicCompletion.map I (Finsupp.lapply a : (A →₀ R) →ₗ[R] R) x) := rfl

/--
概要：自由加群の完備化の埋め込みは元の有限台関数の係数を保つ。
方針：標準完備化写像と座標写像の両立性を使う。
規約：KST §5、Stacks 05BC、元の有限台関数から通常の関数への写像。
使われ方：完備化の埋め込みと元の自由加群の比較。
-/
theorem completedFreeEmbedding_of {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (A : Type*) (v : A →₀ R) :
    completedFreeEmbedding I A (AdicCompletion.of I (A →₀ R) v) = (v : A → R) := by
  funext a
  rw [completedFreeEmbedding_apply]
  simp only [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  rfl

/--
概要：自由加群の完備化から完備な基礎環の積への写像は単射。
方針：完備化座標の単射性と各係数の線形同型を合成する。
規約：KST §5、Stacks 05BC、Noether 性・基底の有限性は不要。
使われ方：普遍単射性を示す前の実際の埋め込み。
-/
theorem completedFreeEmbedding_injective {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (A : Type*) : Function.Injective (completedFreeEmbedding I A) :=
  (LinearEquiv.piCongrRight (fun _ : A => (AdicCompletion.ofLinearEquiv I R).symm)).injective.comp
    (completedFinsuppCoordinates_injective I A R)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
