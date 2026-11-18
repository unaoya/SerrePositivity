module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitCoefficient
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPairNaturality

/-!
# Γ の任意の頂点を単位からの複体射で表す

DAG XIII §2.2 の Ω 比較の零次数への前段。
標準零単体の元の AW 余単位が同型であることを使い、頂点ごとの持ち上げを
選ぶことなく、同じ実随伴の同値で表す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の AW 零単体余単位を、その既証の逆射と束ねる。 -/
def zeroSimplexCounitIso :
    (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌) ≅ 𝟙_ (Complex A) := by
  have := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso A
  exact asIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj ⦋0⦌))

/-- Γ の頂点と単位からの複体射の、指定された全単射。 -/
def gammaVertexUnitHomEquiv (M : Complex A) :
    (gammaModule A M).obj (Opposite.op ⦋0⦌) ≃ (𝟙_ (Complex A) ⟶ M) where
  toFun x := (zeroSimplexCounitIso A).inv ≫
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A M ⦋0⦌).symm x
  invFun f := _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A M ⦋0⦌ ((zeroSimplexCounitIso A).hom ≫ f)
  left_inv x := by
    dsimp only
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Equiv.apply_symm_apply]
  right_inv f := by
    dsimp only
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 同じ頂点からの複体射の回収は、元の複体射に自然。 -/
lemma gammaVertexUnitHomEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    gammaVertexUnitHomEquiv A N
      (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map f).app (Opposite.op ⦋0⦌) x) =
    gammaVertexUnitHomEquiv A M x ≫ f := by
  change (zeroSimplexCounitIso A).inv ≫
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A N ⦋0⦌).symm
      (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map f).app (Opposite.op ⦋0⦌) x) = _
  rw [gammaProbeEquiv_symm_postcomp, ← Category.assoc]
  rfl

/-- 指定単位の頂点の像で、全ての Γ の頂点を厳密に回収できる。 -/
lemma gammaUnit_vertex_generates (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (gammaVertexUnitHomEquiv A M x)).app
      (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌) = x := by
  change ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (gammaVertexUnitHomEquiv A M x)).app
    (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (𝟙_ (Complex A)) ⦋0⦌
        (zeroSimplexCounitIso A).hom) = x
  erw [← _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp]
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A M ⦋0⦌
    ((zeroSimplexCounitIso A).hom ≫ (zeroSimplexCounitIso A).inv ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A M ⦋0⦌).symm x) = x
  rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.EInfinity.PowerOperation
