module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsHom

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
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
    extendMap (_root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he L H f) e ≫
      _root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A e he H = f := by
  subst e
  change (_root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv L H).symm ((_root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv L H) f) = f
  exact (_root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv L H).symm_apply_apply f

lemma normalizedChainsTruncationHomEquiv_inclusion (S : SSet.{0}) (H : Complex A)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) :
    extendMap (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H f) ComplexShape.embeddingDownNat ≫
      _root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H = f :=
  _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape_inclusion A _ _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero _ H f

end SerrePositivity.ComplexLimits
