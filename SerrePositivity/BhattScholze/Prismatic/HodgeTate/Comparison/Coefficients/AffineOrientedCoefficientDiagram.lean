module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 元の向き付き prism 射の mod d 係数変更

## 概要
生成元を単位倍で移す元の prism 射について、元の mod d 模型の係数射を作る。

## 方針
元の各項の環射を、生成元の像が終域の生成元のイデアルに入ることを使って降ろす。

## 規約
生成元の像を終域の選択生成元そのものと仮定しない。

## 使われ方
Construction 6.1 の α(d)=u*p の係数と Bockstein を比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

private theorem affineHTCoefficient_generator_mem (n : SimplexCategory) :
    affineHTCoefficientRingMap f hP hQ r n (htGenerator P hP r n) ∈
      Ideal.span {htGenerator Q hQ r n} := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit
  change (affineHTCoefficientRings f hP hQ r).app n
    ((htBase P hP r).app n P.generator) ∈ _
  rw [affineHTCoefficientRings_base, hu, map_mul]
  exact (Ideal.span {htGenerator Q hQ r n}).mul_mem_right _ (Ideal.subset_span rfl)

/-- 元の向き付き prism 射の、元の mod d 模型の間の係数射。 -/
def affineHTCoefficientReducedAny : reducedModel P hP r ⟶ reducedModel Q hQ r where
  app n := CommRingCat.ofHom (Ideal.quotientMap
    (Ideal.span {htGenerator Q hQ r n ^ (1 : ℕ)}) (affineHTCoefficientRingMap f hP hQ r n)
    (by
      rw [Ideal.span_singleton_le_iff_mem]
      change affineHTCoefficientRingMap f hP hQ r n (htGenerator P hP r n ^ (1 : ℕ)) ∈
        (Ideal.span {htGenerator Q hQ r n ^ (1 : ℕ)} : Ideal ((htRings Q hQ r).obj n))
      simpa only [pow_one] using affineHTCoefficient_generator_mem f hP hQ r n))
  naturality m n θ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ ((affineHTCoefficientRings f hP hQ r).app n
      ((htRings P hP r).map θ x)) =
      Ideal.Quotient.mk _ ((htRings Q hQ r).map θ
        ((affineHTCoefficientRings f hP hQ r).app m x))
    exact congrArg (Ideal.Quotient.mk _)
      (ConcreteCategory.congr_hom ((affineHTCoefficientRings f hP hQ r).naturality θ) x)

/-- 一般の向きの係数射も、元の商の単位上では元の環射そのもの。 -/
theorem affineHTCoefficientReducedAny_mk (n : SimplexCategory) (x : (htRings P hP r).obj n) :
    (affineHTCoefficientReducedAny f hP hQ r).app n
      (Ideal.Quotient.mk (Ideal.span {htGenerator P hP r n ^ (1 : ℕ)}) x) =
      Ideal.Quotient.mk (Ideal.span {htGenerator Q hQ r n ^ (1 : ℕ)})
        (affineHTCoefficientRingMap f hP hQ r n x) := rfl

/-- 生成元を厳密に保つときは、既に使った元の厳密な係数射と一致する。 -/
theorem affineHTCoefficientReducedAny_eq (hg : f.toRingHom P.generator = Q.generator) :
    affineHTCoefficientReducedAny f hP hQ r = affineHTCoefficientReduced f hP hQ r hg := by
  apply NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

end SerrePositivity.BhattScholze.Prismatic
