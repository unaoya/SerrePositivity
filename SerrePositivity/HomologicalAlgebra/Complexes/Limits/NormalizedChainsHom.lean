module

public import SerrePositivity.HomologicalAlgebra.ComplexLimits.ExtendTruncationHomNaturality
public import SerrePositivity.EInfinity.BarrattEccles.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# 実正規化鎖からの Hom と smart 切断の Dold–Kan Hom

概要：既存 normalizedFunctor の実複体からの射を元の単体的加群の射へ同定する。
方針：同じ負次数埋め込みを同定し、延長・切断の Hom 同値と Mathlib Dold–Kan を使う。
規約：零次数の cycles 条件と元の線形化を保持する。
使われ方：複体 frame Hom と dg nerve Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma embeddingDownNat_eq_upIntLE_zero :
    ComplexShape.embeddingDownNat = ComplexShape.embeddingUpIntLE 0 := by
  unfold ComplexShape.embeddingDownNat ComplexShape.embeddingUpIntLE ComplexShape.Embedding.mk'
  congr 1
  funext n
  exact (zero_sub (n : ℤ)).symm

def extendTruncationHomEquivOfShape
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (L : ChainComplex (ModuleCat.{u} A) ℕ)
    (H : Complex A) : (L.extend e ⟶ H) ≃ (L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) := by
  subst e
  exact _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv L H

lemma extendTruncationHomEquivOfShape_precomp
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) {L L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (H : Complex A) (g : L' ⟶ L) (f : L.extend e ⟶ H) :
    _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he L' H (extendMap g e ≫ f) =
      g ≫ _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he L H f := by
  subst e
  exact _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv_precomp H g f

def normalizedChainsTruncationHomEquiv (S : SSet) (H : Complex A) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) ≃
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S) ⟶
          H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :=
  _root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A ComplexShape.embeddingDownNat
    _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero _ H

def normalizedChainsHomEquiv (S : SSet) (H : Complex A) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) ≃
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S ⟶
        (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).obj
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedChainsTruncationHomEquiv A S H).trans
    ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv _ _)

end SerrePositivity.ComplexLimits
