module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedChainsHom

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedChainsTruncationHomEquiv_precomp {S T : SSet} (f : S ⟶ T)
    (H : Complex A) (g : (BarrattEccles.normalizedFunctor A).obj T ⟶ H) :
    normalizedChainsTruncationHomEquiv A S H ((BarrattEccles.normalizedFunctor A).map f ≫ g) =
      (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map
        ((BarrattEccles.linearization A).map f) ≫ normalizedChainsTruncationHomEquiv A T H g :=
  extendTruncationHomEquivOfShape_precomp A ComplexShape.embeddingDownNat
    embeddingDownNat_eq_upIntLE_zero H _ g

lemma normalizedChainsHomEquiv_precomp {S T : SSet} (f : S ⟶ T) (H : Complex A)
    (g : (BarrattEccles.normalizedFunctor A).obj T ⟶ H) :
    normalizedChainsHomEquiv A S H ((BarrattEccles.normalizedFunctor A).map f ≫ g) =
      (BarrattEccles.linearization A).map f ≫ normalizedChainsHomEquiv A T H g := by
  change (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv _ _
      (normalizedChainsTruncationHomEquiv A S H (_ ≫ g)) = _
  rw [normalizedChainsTruncationHomEquiv_precomp]
  exact (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv_naturality_left
      ((BarrattEccles.linearization A).map f) (normalizedChainsTruncationHomEquiv A T H g)

end SerrePositivity.EInfinity.ComplexLimits
