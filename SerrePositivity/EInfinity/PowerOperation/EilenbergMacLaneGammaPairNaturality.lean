module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPair
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedHomTargetNaturality

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
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma gammaProbeEquiv_symm_postcomp {K L : Complex A} (n : SimplexCategory)
    (f : K ⟶ L) (x : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op n)) :
    (normalizedSimplexHomEquiv A L n).symm
      (((truncatedDoldKanFunctor A).map f).app (Opposite.op n) x) =
    (normalizedSimplexHomEquiv A K n).symm x ≫ f := by
  apply (normalizedSimplexHomEquiv A L n).injective
  rw [Equiv.apply_symm_apply, normalizedSimplexHomEquiv_postcomp,
    Equiv.apply_symm_apply]
  rfl

/-- 両方の複体を写してから評価しても、指定されたテンソル射を得る。 -/
lemma gammaPair_naturality {K L K' L' : Complex A} (a : K ⟶ K') (b : L ⟶ L') :
    (((truncatedDoldKanFunctor A).map a) ⊗ₘ
      ((truncatedDoldKanFunctor A).map b)) ≫ gammaPair A K' L' =
    gammaPair A K L ≫ (truncatedDoldKanFunctor A).map (a ⊗ₘ b) := by
  ext n x
  change normalizedSimplexHomEquiv A (K' ⊗ L') n.unop
    (simplexPairEvaluation A n.unop
      ((normalizedSimplexHomEquiv A K' n.unop).symm
        (((truncatedDoldKanFunctor A).map a).app n x.1))
      ((normalizedSimplexHomEquiv A L' n.unop).symm
        (((truncatedDoldKanFunctor A).map b).app n x.2))) = _
  erw [gammaProbeEquiv_symm_postcomp A n.unop a x.1,
    gammaProbeEquiv_symm_postcomp A n.unop b x.2,
    ← simplexPairEvaluation_postcomp, normalizedSimplexHomEquiv_postcomp]
  rfl

end SerrePositivity.EInfinity.PowerOperation
