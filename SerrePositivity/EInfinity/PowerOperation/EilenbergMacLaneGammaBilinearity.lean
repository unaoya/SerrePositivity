module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaAdditivity
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaAxes

/-!
# 実 Γ の二項評価の加法性

DAG XIII §2.2 の loop 比較の前段。AW による指定評価を変えず、各変数で加法を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory MonoidalPreadditive
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma gammaProbeEquiv_symm_add (K : Complex A) (n : SimplexCategory)
    (x y : (gammaModule A K).obj (Opposite.op n)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm (x + y) =
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm x +
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm y := by
  apply (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).injective
  rw [Equiv.apply_symm_apply, gammaProbeEquiv_add,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma simplexPairEvaluation_add_left {K L : Complex A} (n : SimplexCategory)
    (f f' : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K)
    (g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ L) :
    simplexPairEvaluation A n (f + f') g =
      simplexPairEvaluation A n f g + simplexPairEvaluation A n f' g := by
  simp only [simplexPairEvaluation, add_tensor, Preadditive.comp_add]

lemma simplexPairEvaluation_add_right {K L : Complex A} (n : SimplexCategory)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K)
    (g g' : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ L) :
    simplexPairEvaluation A n f (g + g') =
      simplexPairEvaluation A n f g + simplexPairEvaluation A n f g' := by
  simp only [simplexPairEvaluation, tensor_add, Preadditive.comp_add]

/-- 二項評価の値を、同じ Γ の加群の元として読む。 -/
abbrev gammaPairValue (K L : Complex A) (n : SimplexCategory)
    (x : (gammaModule A K).obj (Opposite.op n))
    (y : (gammaModule A L).obj (Opposite.op n)) :
    (gammaModule A (K ⊗ L)).obj (Opposite.op n) :=
  (gammaPair A K L).app (Opposite.op n) (x, y)

lemma gammaPair_add_left (K L : Complex A) (n : SimplexCategory)
    (x x' : (gammaModule A K).obj (Opposite.op n))
    (y : (gammaModule A L).obj (Opposite.op n)) :
    gammaPairValue A K L n (x + x') y =
      gammaPairValue A K L n x y +
        gammaPairValue A K L n x' y := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (K ⊗ L) n
    (simplexPairEvaluation A n
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm (x + x'))
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).symm y)) = _
  rw [gammaProbeEquiv_symm_add, simplexPairEvaluation_add_left, gammaProbeEquiv_add]
  rfl

lemma gammaPair_add_right (K L : Complex A) (n : SimplexCategory)
    (x : (gammaModule A K).obj (Opposite.op n))
    (y y' : (gammaModule A L).obj (Opposite.op n)) :
    gammaPairValue A K L n x (y + y') =
      gammaPairValue A K L n x y +
        gammaPairValue A K L n x y' := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (K ⊗ L) n
    (simplexPairEvaluation A n
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm x)
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).symm (y + y'))) = _
  rw [gammaProbeEquiv_symm_add, simplexPairEvaluation_add_right, gammaProbeEquiv_add]
  rfl

end SerrePositivity.EInfinity.PowerOperation
