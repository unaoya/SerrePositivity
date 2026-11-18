module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaBilinearity
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounitLaws

/-!
# AW の余単位で定める Γ の指定単位

DAG XIII §2.2 の基本円の照合への前段。
単位の単体は元の AW 余単位の随伴像として定め、右単位則も同じ射で証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 指定単体の AW 余単位の、同じ実随伴による像。零基点とは異なる単位の元。 -/
def gammaUnitSimplex (n : SimplexCategory) :
    (gammaModule A (𝟙_ (Complex A))).obj (Opposite.op n) :=
  _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (𝟙_ (Complex A)) n
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n))

lemma simplexPairEvaluation_right_unit {K : Complex A} (n : SimplexCategory)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K) :
    simplexPairEvaluation A n f
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)) ≫ (ρ_ K).hom = f := by
  let C := (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)
  let e : C ⟶ 𝟙_ (Complex A) :=
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (SSet.stdSimplex.obj n) ≫
    (f ⊗ₘ e) ≫ (ρ_ K).hom = f
  rw [show f ⊗ₘ e = (𝟙 C ⊗ₘ e) ≫ (f ⊗ₘ 𝟙 (𝟙_ (Complex A))) by
    rw [tensorHom_comp_tensorHom]
    erw [Category.id_comp, Category.comp_id]]
  have hr : (f ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ (ρ_ K).hom = (ρ_ C).hom ≫ f := by
    simpa only [tensorHom_id] using rightUnitor_naturality f
  simp only [Category.assoc]
  slice_lhs 3 4 => exact hr
  rw [← Category.assoc]
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (SSet.stdSimplex.obj n) ≫
    (𝟙 C ⊗ₘ e) ≫ (ρ_ C).hom) ≫ f = f
  have hc : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A (SSet.stdSimplex.obj n) ≫
      (𝟙 C ⊗ₘ e) ≫ (ρ_ C).hom = 𝟙 C :=
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_right_counit A (SSet.stdSimplex.obj n)
  rw [hc, Category.id_comp]

/-- 指定 Γ の二項評価は、指定 AW 単位を本当の右単位として保つ。 -/
lemma gammaPair_right_unit (K : Complex A) (n : SimplexCategory)
    (x : (gammaModule A K).obj (Opposite.op n)) :
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (ρ_ K).hom).app (Opposite.op n)
      (gammaPairValue A K (𝟙_ (Complex A)) n x (gammaUnitSimplex A n)) = x := by
  change ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (ρ_ K).hom).app (Opposite.op n)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (K ⊗ 𝟙_ (Complex A)) n
      (simplexPairEvaluation A n ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm x)
        ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (𝟙_ (Complex A)) n).symm
          (gammaUnitSimplex A n)))) = x
  rw [gammaUnitSimplex, Equiv.symm_apply_apply]
  erw [← _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp, simplexPairEvaluation_right_unit,
    Equiv.apply_symm_apply]

end SerrePositivity.EInfinity.PowerOperation
