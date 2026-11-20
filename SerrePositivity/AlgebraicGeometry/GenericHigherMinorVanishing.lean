module

public import SerrePositivity.AlgebraicGeometry.LocalGenericComparison
public import Mathlib.RingTheory.FiniteType

/-!
概要：KST §5、Stacks 0810 の一定の一般階数による高次小行列式の消滅。
方針：拡大素点局所化での自由階数の計算と、特別な局所環の族による消滅判定を接続する。
規約：関係式行列は実際の生成全射の核全体を生成する。
使われ方：正則な小行列式による純変換の自由性判定。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：一定の一般自由階数を持つ相対平坦な有限加群の高次関係式小行列式イデアルは零。
方針：各拡大素点の自由階数から局所的消滅を得て、分裂表示による大域的消滅判定を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、有限表示性は Noether 性から導く。
使われ方：係数中心の blowup チャートで純変換の自由性を判定する。
-/
theorem higherMinorIdeal_eq_bot_of_constant_genericRank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Flat A M] [Module.Finite B M]
    [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q) (H : Matrix m n B)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q) (r : ℕ)
    (hrank : ∀ P : PrimeSpectrum A,
      let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
      Module.finrank L (L ⊗[B] M) = r)
    (k : ℕ) (hk : Fintype.card m - r < k) : matrixMinorIdeal H k = ⊥ := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  apply ideal_eq_bot_of_genericPrime_maps_eq_bot A B e p hpe
  intro P
  let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
  have hr : Module.finrank L (L ⊗[B] M) = r := hrank P
  have hdegree : Fintype.card m - Module.finrank L (L ⊗[B] M) < k := by
    simpa only [hr] using hk
  exact (minor_pattern_at_geometricallyIntegralGenericPrime A B P q hq H hH).2 k hdegree

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
