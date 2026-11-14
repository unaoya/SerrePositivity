module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPair
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# 実 Dold–Kan の標準単体評価と零元

DAG XIII §2.2 の構造射を基点付き写像へ移すための照合。
同じ延長・smart 切断・実随伴を使い、Γ の零元を別の選択へ取り替えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma extendTruncationHomEquiv_map_zero (L : ChainComplex (ModuleCat A) ℕ)
    (K : Complex A) : extendTruncationHomEquiv L K 0 = 0 := by
  apply (extendTruncationHomEquiv L K).symm.injective
  rw [Equiv.symm_apply_apply]
  change (0 : L.extend (ComplexShape.embeddingUpIntLE 0) ⟶ K) =
    ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat A)).map 0 ≫ _ ≫ _
  simp only [Functor.map_zero, zero_comp]

lemma normalizedChainsTruncationHomEquiv_map_zero (S : SSet.{0}) (K : Complex A) :
    normalizedChainsTruncationHomEquiv A S K 0 = 0 := by
  have hz (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
      (he : e = ComplexShape.embeddingUpIntLE 0)
      (L : ChainComplex (ModuleCat A) ℕ) :
      extendTruncationHomEquivOfShape A e he L K 0 = 0 := by
    subst e
    exact extendTruncationHomEquiv_map_zero A L K
  exact hz _ _ _

lemma normalizedChainsHomEquiv_map_zero (S : SSet.{0}) (K : Complex A) :
    normalizedChainsHomEquiv A S K 0 = 0 := by
  change (Abelian.DoldKan.equivalence.toAdjunction.homEquiv _ _)
    (normalizedChainsTruncationHomEquiv A S K 0) = 0
  rw [normalizedChainsTruncationHomEquiv_map_zero]
  simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- 指定標準単体の評価は、零鎖写像を実 Γ の零元へ送る。 -/
lemma gammaProbeEquiv_zero (K : Complex A) (n : SimplexCategory) :
    normalizedSimplexHomEquiv A K n 0 =
      (0 : ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
        SimplicialObject (ModuleCat A)).obj
          (K.truncLE' (ComplexShape.embeddingUpIntLE 0))).obj (Opposite.op n)) := by
  change linearizedSimplexHomEquiv A _ n
    (normalizedChainsHomEquiv A (SSet.stdSimplex.obj n) K 0) = _
  rw [normalizedChainsHomEquiv_map_zero]
  rfl

/-- 零単体の逆像も、指定された零鎖写像である。 -/
lemma gammaProbeEquiv_symm_zero (K : Complex A) (n : SimplexCategory) :
    (normalizedSimplexHomEquiv A K n).symm
      (0 : ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
        SimplicialObject (ModuleCat A)).obj
          (K.truncLE' (ComplexShape.embeddingUpIntLE 0))).obj (Opposite.op n)) = 0 := by
  apply (normalizedSimplexHomEquiv A K n).injective
  rw [Equiv.apply_symm_apply, gammaProbeEquiv_zero]

end SerrePositivity.EInfinity.PowerOperation
