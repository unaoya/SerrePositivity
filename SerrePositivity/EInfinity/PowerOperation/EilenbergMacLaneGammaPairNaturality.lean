module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPair
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality

/-!
# Γ の二項積の両変数での自然性

DAG XIII §2.2 のスペクトル構造射への準備。指定された有限単体の評価を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma gammaProbeEquiv_symm_postcomp {K L : Complex A} (n : SimplexCategory)
    (f : K ⟶ L) (x : ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj K).obj (Opposite.op n)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).symm
      (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map f).app (Opposite.op n) x) =
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm x ≫ f := by
  apply (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).injective
  rw [Equiv.apply_symm_apply, _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp,
    Equiv.apply_symm_apply]
  rfl

/-- 両方の複体を写してから評価しても、指定されたテンソル射を得る。 -/
lemma gammaPair_naturality {K L K' L' : Complex A} (a : K ⟶ K') (b : L ⟶ L') :
    (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map a) ⊗ₘ
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map b)) ≫ gammaPair A K' L' =
    gammaPair A K L ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (a ⊗ₘ b) := by
  ext n x
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (K' ⊗ L') n.unop
    (simplexPairEvaluation A n.unop
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K' n.unop).symm
        (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map a).app n x.1))
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L' n.unop).symm
        (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map b).app n x.2))) = _
  erw [gammaProbeEquiv_symm_postcomp A n.unop a x.1,
    gammaProbeEquiv_symm_postcomp A n.unop b x.2,
    ← simplexPairEvaluation_postcomp, _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp]
  rfl

end SerrePositivity.EInfinity.PowerOperation
