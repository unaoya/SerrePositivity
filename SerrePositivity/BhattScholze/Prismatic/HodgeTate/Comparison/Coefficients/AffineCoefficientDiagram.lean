module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineEnvelopeCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel

/-!
# 元の affine 余単体模型の係数射

## 概要
prism 射の各項の係数変更を、既存の Hodge–Tate 模型の間の自然変換にする。

## 方針
包の普遍性による各項の射と、全単体射についての既存の自然性を使う。

## 規約
始域と終域の濃度上限は元の模型が選んだものを使い、それらの一致を要求しない。

## 使われ方
特定の Zp 係数射の底変換と、普遍基底への比較の指定された脚。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の affine 包の項の間の、指定された係数変更。 -/
def affineHTCoefficientRingMap (n : SimplexCategory) :
    (htRings P hP r).obj n →+* (htRings Q hQ r).obj n :=
  affineEnvelopeCoefficientMap f
    (affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl)
    (affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl)

/-- 同じ係数変更を束ねた、元の余単体的環模型の間の自然変換。 -/
def affineHTCoefficientRings : htRings P hP r ⟶ htRings Q hQ r where
  app n := CommRingCat.ofHom (affineHTCoefficientRingMap f hP hQ r n)
  naturality m n θ := by
    apply CommRingCat.hom_ext
    exact affineEnvelopeCoefficientMap_natural f
      (affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl)
      (affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl)
      (affineEnvelopeTerm P hP r m.len (cutoff A (affineAlgebra P r)) le_rfl)
      (affineEnvelopeTerm Q hQ r m.len (cutoff B (affineAlgebra Q r)) le_rfl) θ

/-- 係数変更の基底脚は、与えられた prism 射との合成である。 -/
theorem affineHTCoefficientRings_base (n : SimplexCategory) (a : A) :
    (affineHTCoefficientRings f hP hQ r).app n ((htBase P hP r).app n a) =
      (htBase Q hQ r).app n (f.toRingHom a) := by
  exact RingHom.congr_fun
    (affineEnvelopeCoefficientMap_spec f _ _).2.1 a

/-- 選択生成元を厳密に保つ射では、元の各項の生成元も厳密に保たれる。 -/
theorem affineHTCoefficientRings_generator (hg : f.toRingHom P.generator = Q.generator)
    (n : SimplexCategory) :
    (affineHTCoefficientRings f hP hQ r).app n (htGenerator P hP r n) =
      htGenerator Q hQ r n := by
  exact (affineHTCoefficientRings_base f hP hQ r n P.generator).trans
    (congrArg ((htBase Q hQ r).app n) hg)

/-- 選択生成元を保つ場合の、元の mod d 模型の間の射。 -/
def affineHTCoefficientReduced (hg : f.toRingHom P.generator = Q.generator) :
    reducedModel P hP r ⟶ reducedModel Q hQ r :=
  SerrePositivity.Cosimplicial.quotPowMap _ _ _ _ (htGenerator_nat Q hQ r)
    (affineHTCoefficientRings f hP hQ r) (affineHTCoefficientRings_generator f hP hQ r hg) 1

end SerrePositivity.BhattScholze.Prismatic
