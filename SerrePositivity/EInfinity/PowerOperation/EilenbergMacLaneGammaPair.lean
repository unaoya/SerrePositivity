module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneProbePair
public import SerrePositivity.EInfinity.ComplexLimits.TruncatedDoldKanFunctor

/-!
# 実 Γ の段の二項評価

DAG XIII §2.2 の構造射の単体的な前段。
有限標準単体上の同じ AW 対角と実 Dold–Kan 随伴を用い、全ての単体射で可換な写像を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 実随伴の逆は、同じ Γ の単体射を標準単体の前合成へ送る。 -/
lemma gammaProbeEquiv_symm_map (K : Complex A) {n m : SimplexCategory}
    (θ : n ⟶ m) (x : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op m)) :
    (normalizedSimplexHomEquiv A K n).symm
      (((truncatedDoldKanFunctor A).obj K).map θ.op x) =
    (BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ) ≫
      (normalizedSimplexHomEquiv A K m).symm x := by
  apply (normalizedSimplexHomEquiv A K n).injective
  rw [Equiv.apply_symm_apply, normalizedSimplexHomEquiv_naturality,
    Equiv.apply_symm_apply]
  rfl

/-- 指定標準単体での二項評価は、実 Γ の単体集合の写像を与える。 -/
def gammaPair (K L : Complex A) :
    (truncatedDoldKanFunctor A).obj K ⊗ (truncatedDoldKanFunctor A).obj L ⟶
      (truncatedDoldKanFunctor A).obj (K ⊗ L) where
  app n := ↾fun x => normalizedSimplexHomEquiv A (K ⊗ L) n.unop
    (simplexPairEvaluation A n.unop
      ((normalizedSimplexHomEquiv A K n.unop).symm x.1)
      ((normalizedSimplexHomEquiv A L n.unop).symm x.2))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change normalizedSimplexHomEquiv A (K ⊗ L) m.unop
      (simplexPairEvaluation A m.unop
        ((normalizedSimplexHomEquiv A K m.unop).symm
          (((truncatedDoldKanFunctor A).obj K).map θ x.1))
        ((normalizedSimplexHomEquiv A L m.unop).symm
          (((truncatedDoldKanFunctor A).obj L).map θ x.2))) = _
    erw [gammaProbeEquiv_symm_map A K θ.unop x.1,
      gammaProbeEquiv_symm_map A L θ.unop x.2,
      ← simplexPairEvaluation_precomp, normalizedSimplexHomEquiv_naturality]
    rfl

end SerrePositivity.EInfinity.PowerOperation
