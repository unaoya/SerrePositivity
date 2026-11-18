module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncationInclusionNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom

/-!
# 実正規化 Hom 同値の標的変数への自然性

概要：元の複体射の後合成は、同じ smart 切断と実 Γ の射へ移る。
方針：実延長・切断比較、Dold–Kan 随伴、同じ自由単体評価の自然性を合成する。
規約：元の truncLE'Map と Γ.map の射を保つ。
使われ方：標準自由単位の実 Hom 比較との整合。
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

lemma extendTruncationHomEquivOfShape_postcomp
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (P : ChainComplex (ModuleCat.{u} A) ℕ)
    {K L : Complex A} (f : P.extend e ⟶ K) (g : K ⟶ L) :
    _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he P L (f ≫ g) =
      _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he P K f ≫
        truncLE'Map g (ComplexShape.embeddingUpIntLE 0) := by
  subst e
  exact _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv_postcomp P f g

lemma normalizedChainsTruncationHomEquiv_postcomp (S : SSet) {K L : Complex A}
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ K) (g : K ⟶ L) :
    _root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S L (f ≫ g) =
      _root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S K f ≫
        truncLE'Map g (ComplexShape.embeddingUpIntLE 0) :=
  _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape_postcomp A ComplexShape.embeddingDownNat
    _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero _ f g

lemma normalizedChainsHomEquiv_postcomp (S : SSet) {K L : Complex A}
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ K) (g : K ⟶ L) :
    _root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A S L (f ≫ g) = _root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A S K f ≫
      (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
        (truncLE'Map g (ComplexShape.embeddingUpIntLE 0)) := by
  change (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv _ _
      (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S L (f ≫ g)) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv_postcomp]
  exact (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv_naturality_right _ _

lemma linearizedSimplexHomEquiv_postcomp {M N : SimplicialObject (ModuleCat.{u} A)}
    (n : SimplexCategory) (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
      (SSet.stdSimplex.obj n) ⟶ M) (g : M ⟶ N) :
    _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A N n (f ≫ g) =
      g.app (Opposite.op n) (_root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A M n f) := rfl

lemma normalizedSimplexHomEquiv_postcomp {K L : Complex A} (n : SimplexCategory)
    (f : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K) (g : K ⟶ L) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n (f ≫ g) =
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
        SimplicialObject (ModuleCat A)).map
          (truncLE'Map g (ComplexShape.embeddingUpIntLE 0))).app (Opposite.op n)
            (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n f) := by
  change _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A _ n (_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A _ L (f ≫ g)) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv_postcomp]
  exact _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv_postcomp A n _ _

end SerrePositivity.ComplexLimits
