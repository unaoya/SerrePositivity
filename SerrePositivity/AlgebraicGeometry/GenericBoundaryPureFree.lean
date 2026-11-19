module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.CoefficientPrimeBoundaryFree
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralExtendedPrime

/-!
概要：KST §5、Stacks 0810 の係数環上の全拡大素点での境界純変換の自由性。
方針：実際の局所環での自由性と階数を述語にし、係数イデアルの判定を適用する。
規約：述語は局所自由性の結論を保持し、存在定理の仮定としては導入しない。
使われ方：大きい Rees チャート環への適用で局所環の型を繰り返し展開せずに結論を運ぶ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数環の全素点の拡大局所環で境界純変換が指定した階数の自由加群であるという結論。
方針：幾何学的整性から実際の拡大素点を取り、純変換の自由性と有限階数を同時に述べる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の代数からの作用を明示する。
使われ方：係数中心の全チャートの一般点での自由性を保持する。
-/
def GenericBoundaryPureFree (A B C : Type u) (M : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsNoetherianRing C] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] (f : C) (r : ℕ) : Prop :=
  let D := C ⊗[A] B
  ∀ P : PrimeSpectrum C,
    letI : (P.asIdeal.map (algebraMap C D)).IsPrime :=
      ideal_map_tensor_isPrime_of_geometricallyIntegral A B C P.asIdeal
    let L := Localization.AtPrime (P.asIdeal.map (algebraMap C D))
    let φ : B →+* L := (algebraMap D L).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
    letI : Algebra B L := φ.toAlgebra
    Module.Free L (modulePureTransform (algebraMap D L (algebraMap C D f)) (L ⊗[B] M)) ∧
      Module.finrank L
        (modulePureTransform (algebraMap D L (algebraMap C D f)) (L ⊗[B] M)) = r

/--
概要：正則単項化した係数イデアルと高次消滅から全拡大素点での境界純変換の自由性を得る。
方針：幾何学的整性で拡大素性を充足し、既証の局所自由性判定を各素点に適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、述語はここで実証明する結論。
使われ方：実際の blowup チャートへの適用を局所環の型の展開から分ける。
-/
theorem genericBoundaryPureFree_of_coefficient_minor
    {A B C : Type u} {M ι m n : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
    [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (H : Matrix m n B) (k : ℕ) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥)
    (c f : C) (hc : IsRegular c) (hf : IsRegular f) (N : ℕ) (hcf : c ∣ f ^ N)
    (hcoeff : (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k)).map (algebraMap A C) =
      Ideal.span {c}) : GenericBoundaryPureFree A B C M f (Fintype.card m - k) := by
  dsimp only [GenericBoundaryPureFree]
  intro P
  let : (P.asIdeal.map (algebraMap C (C ⊗[A] B))).IsPrime :=
    ideal_map_tensor_isPrime_of_geometricallyIntegral A B C P.asIdeal
  exact coefficient_prime_boundary_free_and_finrank (A := A) (B := B) (C := C) (M := M)
    e p hpe H k q hq hH hzero c f hc hf N hcf hcoeff
    P.asIdeal (inferInstance : P.asIdeal.IsPrime).ne_top

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
