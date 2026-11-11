module

public import SerrePositivity.BhattScholze.Prismatic.PrismaticFrameCoproduct
public import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
public import SerrePositivity.BhattScholze.Prismatic.AffineCechVertexFrame
public import SerrePositivity.BhattScholze.Prismatic.CechAlexanderSmall
import all SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction

/-!
# 有限 affine Čech–Alexander 模型の Čech データ

## 概要
有限 affine 包の標準余積と弱始性を、小さい site の Čech データへ渡す。
## 方針
既存の affineCechVertexFrame を使い、持ち上げの証明は繰り返さない。
## 規約
BS 著者版 Construction 4.17–4.18。通常の圏の主張のみを扱う。
## 使われ方
小さい affine 模型による後の prismatic 計算の入力。
-/

public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hP : IsBoundedPrism P) (r : ℕ) (κ : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)

/-- Construction 4.17：有限 affine 模型の標準頂点は余積を与える。 -/
def cechAlexanderAffine_isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk ((cechAlexanderAffine P hP r κ hκ).obj ⦋n⦌)
      (fun i : Fin (n + 1) => (cechAlexanderAffine P hP r κ hκ).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) :=
  (affineCechVertexFrame P (fun n => affineEnvelopeTerm P hP r n κ hκ)).isCoproduct n

/-- Construction 4.17：有限 affine 模型の各項は弱始対象。 -/
theorem cechAlexanderAffine_weaklyInitial (n : ℕ) : CategoryTheory.IsWeaklyInitial
    ((cechAlexanderAffine P hP r κ hκ).obj ⦋n⦌) :=
  (affineCechVertexFrame P (fun n => affineEnvelopeTerm P hP r n κ hκ)).weaklyInitial n

variable [EssentiallySmall.{u} (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)]

/-- Construction 4.18：有限 affine 模型から作る小さい site の Čech データ。 -/
def affineCechNerveData : CategoryTheory.CechNerveData
    (Opposite.op ((equivSmallModel (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)).functor.obj
      ((cechAlexanderAffine P hP r κ hκ).obj ⦋0⦌))) :=
  smallCechNerveOfCoproducts P _ κ _ (cechAlexanderAffine_isCoproduct P hP r κ hκ)

/-- 小さい site の向きでは有限 affine 模型の零次は弱終対象。 -/
theorem affineCechSmall_weaklyTerminal : CategoryTheory.IsWeaklyTerminal
    (Opposite.op ((equivSmallModel (PrismOver P (prismPolynomialCompletion P (Fin r)) κ)).functor.obj
      ((cechAlexanderAffine P hP r κ hκ).obj ⦋0⦌))) :=
  CategoryTheory.CechNerveData.weaklyTerminal_small
    (cechAlexanderAffine_weaklyInitial P hP r κ hκ 0)

end SerrePositivity.BhattScholze.Prismatic
