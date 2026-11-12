module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaZero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# 実 Γ の標準単体評価は加法を保つ

DAG XIII §2.2 の指定構造射を加法的な loop 比較へ接続する前段。
実延長・smart 切断・Dold–Kan 随伴を変えずに加法を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma extendTruncationHomEquiv_symm_add (P : ChainComplex (ModuleCat A) ℕ)
    (K : Complex A) (f g : P ⟶ K.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    (extendTruncationHomEquiv P K).symm (f + g) =
      (extendTruncationHomEquiv P K).symm f +
        (extendTruncationHomEquiv P K).symm g := by
  change ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat A)).map (f + g) ≫
    (K.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫ K.ιTruncLE 0 = _
  simp only [Functor.map_add, Preadditive.add_comp]
  rfl

lemma extendTruncationHomEquiv_add (P : ChainComplex (ModuleCat A) ℕ)
    (K : Complex A) (f g : P.extend (ComplexShape.embeddingUpIntLE 0) ⟶ K) :
    extendTruncationHomEquiv P K (f + g) =
      extendTruncationHomEquiv P K f + extendTruncationHomEquiv P K g := by
  apply (extendTruncationHomEquiv P K).symm.injective
  rw [Equiv.symm_apply_apply, extendTruncationHomEquiv_symm_add,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma normalizedChainsHomEquiv_add (S : SSet.{0}) (K : Complex A)
    (f g : (BarrattEccles.normalizedFunctor A).obj S ⟶ K) :
    normalizedChainsHomEquiv A S K (f + g) =
      normalizedChainsHomEquiv A S K f + normalizedChainsHomEquiv A S K g := by
  have ht (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
      (he : e = ComplexShape.embeddingUpIntLE 0) (P : ChainComplex (ModuleCat A) ℕ)
      (f g : P.extend e ⟶ K) :
      extendTruncationHomEquivOfShape A e he P K (f + g) =
        extendTruncationHomEquivOfShape A e he P K f +
          extendTruncationHomEquivOfShape A e he P K g := by
    subst e
    exact extendTruncationHomEquiv_add A P K f g
  have : (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  change Abelian.DoldKan.equivalence.toAdjunction.homEquiv _ _
    (normalizedChainsTruncationHomEquiv A S K (f + g)) = _
  rw [show normalizedChainsTruncationHomEquiv A S K (f + g) =
    normalizedChainsTruncationHomEquiv A S K f +
      normalizedChainsTruncationHomEquiv A S K g from ht _ _ _ f g]
  exact Abelian.DoldKan.equivalence.toAdjunction.homAddEquiv_add _ _ _ _

lemma gammaProbeEquiv_add (K : Complex A) (n : SimplexCategory)
    (f g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K) :
    normalizedSimplexHomEquiv A K n (f + g) =
      normalizedSimplexHomEquiv A K n f + normalizedSimplexHomEquiv A K n g := by
  change linearizedSimplexHomEquiv A _ n
    (normalizedChainsHomEquiv A (SSet.stdSimplex.obj n) K (f + g)) = _
  rw [normalizedChainsHomEquiv_add]
  rfl

end SerrePositivity.EInfinity.PowerOperation
