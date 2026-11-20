module

public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralExtendedPrime
public import SerrePositivity.AlgebraicGeometry.ExtendedPrimeLocalFreeness
public import SerrePositivity.AlgebraicGeometry.BaseChangedMinorFreeCriterion

/-!
概要：KST §5、Stacks 0810 の幾何学的整な代数における拡大素点と表示行列。
方針：拡大素性と相対平坦加群の自由性を接続し、小行列式の条件を得る。
規約：有限表示加群の階数は特別な局所環で計算する。
使われ方：境界外の平坦性から係数中心を選ぶための幾何学的入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/--
概要：幾何学的整な平坦有限表示代数で基礎環の素点から得る拡大素点。
方針：拡大イデアルが素である既証の幾何学的補題を使う。
規約：KST §5、Stacks 0810、基礎環は Noether とする。
使われ方：ファイバーの一般点に対応する特別な局所化を実際に構成する。
-/
def geometricallyIntegralGenericPrime (P : PrimeSpectrum A) : PrimeSpectrum B :=
  ⟨P.asIdeal.map (algebraMap A B), ideal_map_isPrime_of_geometricallyIntegral A B P.asIdeal⟩

/--
概要：幾何学的整な代数の拡大素点は元の素点の上にある。
方針：幾何学的整な射の全射性から拡大・縮約の等式を得る。
規約：KST §5、Stacks 0810、素点の等式として述べる。
使われ方：拡大素点を基礎スキーム上の一般点として比較する。
-/
theorem geometricallyIntegralGenericPrime_comap (P : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap A B) (geometricallyIntegralGenericPrime A B P) = P := by
  have hs : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).surjective
  apply PrimeSpectrum.ext
  exact (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mp (hs P)

variable {M : Type*} [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M] [Module.Flat A M] [Module.FinitePresentation B M]

/--
概要：基礎環上平坦な有限表示加群は幾何学的整な代数の拡大素点で自由。
方針：実際の拡大素点に拡大極大イデアルによる自由性判定を適用する。
規約：KST §5、Stacks 0810、加群の基礎環上の平坦性を使う。
使われ方：選んだ有限表示の小行列式から係数中心を構成する。
-/
theorem free_at_geometricallyIntegralGenericPrime (P : PrimeSpectrum A) :
    Module.Free (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal)
      ((Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal) ⊗[B] M) := by
  let : (P.asIdeal.map (algebraMap A B)).IsPrime :=
    ideal_map_isPrime_of_geometricallyIntegral A B P.asIdeal
  exact free_at_extended_prime (M := M) P.asIdeal

/--
概要：幾何学的整な代数の拡大素点で表示行列の小行列式は自由階数に対応する単位・零条件を満たす。
方針：拡大素点での実際の自由性を任意の有限表示の基底変更に適用する。
規約：KST §5、Stacks 0810、階数の局所定数性はこの補題には仮定しない。
使われ方：局所階数が一定となる開集合上で admissible な係数中心を選ぶ。
-/
theorem minor_pattern_at_geometricallyIntegralGenericPrime
    {m n : Type*} [Fintype m] [Finite n]
    (P : PrimeSpectrum A) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (H : Matrix m n B) (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q) :
    let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
    (matrixMinorIdeal H (Fintype.card m - Module.finrank L (L ⊗[B] M))).map
        (algebraMap B L) = ⊤ ∧
      ∀ j, Fintype.card m - Module.finrank L (L ⊗[B] M) < j →
        (matrixMinorIdeal H j).map (algebraMap B L) = ⊥ := by
  let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
  let : Module.Free L (L ⊗[B] M) := free_at_geometricallyIntegralGenericPrime A B P
  exact minorIdeal_images_at_tensor_finrank H q hq hH

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
