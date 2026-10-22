module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedChainsHom

/-!
# 同じ延長と smart 切断 Hom 同値の元の射の回収

概要：同じ切断 Hom 像を延長し、元の切断包含で合成すると元の複体射になる。
方針：元の実 Hom 同値の逆の定義と左右逆を使う。
規約：負次数の埋め込みの同じ等式を明示する。
使われ方：正規化 Hom の零次数像を元の複体射の値へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def truncationExtendedInclusionOfShape
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (H : Complex A) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extend e ⟶ H := by
  subst e
  exact (H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫ H.ιTruncLE 0

lemma extendTruncationHomEquivOfShape_inclusion
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (L : ChainComplex (ModuleCat.{u} A) ℕ)
    (H : Complex A) (f : L.extend e ⟶ H) :
    extendMap (extendTruncationHomEquivOfShape A e he L H f) e ≫
      truncationExtendedInclusionOfShape A e he H = f := by
  subst e
  change (extendTruncationHomEquiv L H).symm ((extendTruncationHomEquiv L H) f) = f
  exact (extendTruncationHomEquiv L H).symm_apply_apply f

lemma normalizedChainsTruncationHomEquiv_inclusion (S : SSet.{0}) (H : Complex A)
    (f : (BarrattEccles.normalizedFunctor A).obj S ⟶ H) :
    extendMap (normalizedChainsTruncationHomEquiv A S H f) ComplexShape.embeddingDownNat ≫
      truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
        embeddingDownNat_eq_upIntLE_zero H = f :=
  extendTruncationHomEquivOfShape_inclusion A _ embeddingDownNat_eq_upIntLE_zero _ H f

end SerrePositivity.EInfinity.ComplexLimits
