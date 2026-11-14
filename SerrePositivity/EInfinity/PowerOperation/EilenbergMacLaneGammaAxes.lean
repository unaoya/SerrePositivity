module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaZero
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Γ の積は二つの零軸を潰す

DAG XIII §2.2 の基点付き構造射の前段。有限標準単体の同じ AW 評価を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalPreadditive
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 同じ smart 切断の実 Γ。零元の型もこの単体的加群から読む。 -/
abbrev gammaModule (K : Complex A) : SimplicialObject (ModuleCat A) :=
  (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
    SimplicialObject (ModuleCat A)).obj (K.truncLE' (ComplexShape.embeddingUpIntLE 0))

lemma simplexPairEvaluation_zero_left {K L : Complex A} (n : SimplexCategory)
    (g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ L) :
    simplexPairEvaluation A n (0 : _ ⟶ K) g = 0 := by
  simp only [simplexPairEvaluation, zero_tensor, comp_zero]

lemma simplexPairEvaluation_zero_right {K L : Complex A} (n : SimplexCategory)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K) :
    simplexPairEvaluation A n f (0 : _ ⟶ L) = 0 := by
  simp only [simplexPairEvaluation, tensor_zero, comp_zero]

lemma gammaPair_zero_left (K L : Complex A) (n : SimplexCategory)
    (y : (gammaModule A L).obj (Opposite.op n)) :
    (gammaPair A K L).app (Opposite.op n)
      ((0 : (gammaModule A K).obj (Opposite.op n)), y) =
        (0 : (gammaModule A (K ⊗ L)).obj (Opposite.op n)) := by
  change normalizedSimplexHomEquiv A (K ⊗ L) n
    (simplexPairEvaluation A n
      ((normalizedSimplexHomEquiv A K n).symm
        (0 : (gammaModule A K).obj (Opposite.op n)))
      ((normalizedSimplexHomEquiv A L n).symm y)) = _
  rw [gammaProbeEquiv_symm_zero, simplexPairEvaluation_zero_left, gammaProbeEquiv_zero]

lemma gammaPair_zero_right (K L : Complex A) (n : SimplexCategory)
    (x : (gammaModule A K).obj (Opposite.op n)) :
    (gammaPair A K L).app (Opposite.op n)
      (x, (0 : (gammaModule A L).obj (Opposite.op n))) =
        (0 : (gammaModule A (K ⊗ L)).obj (Opposite.op n)) := by
  change normalizedSimplexHomEquiv A (K ⊗ L) n
    (simplexPairEvaluation A n ((normalizedSimplexHomEquiv A K n).symm x)
      ((normalizedSimplexHomEquiv A L n).symm
        (0 : (gammaModule A L).obj (Opposite.op n)))) = _
  rw [gammaProbeEquiv_symm_zero, simplexPairEvaluation_zero_right, gammaProbeEquiv_zero]

end SerrePositivity.EInfinity.PowerOperation
