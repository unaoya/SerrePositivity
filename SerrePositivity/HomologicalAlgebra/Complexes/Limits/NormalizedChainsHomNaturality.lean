module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsHom

/-!
# 正規化鎖の Hom 同値の元の単体集合の射への自然性

概要：同じ実正規化写像による前合成を、元の線形化写像による前合成へ移す。
方針：埋め込みの等号による輸送を抽象化し、実延長と Dold–Kan 随伴の自然性を使う。
規約：全次数の元の単体作用素を保持する。
使われ方：標準単体テンソル Hom の単体集合同型。
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

lemma normalizedChainsTruncationHomEquiv_precomp {S T : SSet} (f : S ⟶ T)
    (H : Complex A) (g : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj T ⟶ H) :
    _root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f ≫ g) =
      (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f) ≫ _root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A T H g :=
  _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape_precomp A ComplexShape.embeddingDownNat
    _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H _ g

lemma normalizedChainsHomEquiv_precomp {S T : SSet} (f : S ⟶ T) (H : Complex A)
    (g : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj T ⟶ H) :
    _root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A S H ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f ≫ g) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f ≫ _root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A T H g := by
  change (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv _ _
      (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H (_ ≫ g)) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv_precomp]
  exact (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv_naturality_left
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f) (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A T H g)

end SerrePositivity.ComplexLimits
