module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnit

/-!
# Γ の指定単位の全単体の点

DAG XIII §2.2 の基本円の照合への前段。零基点を単位に置き換えるのではなく、
同じ Γ の台の非基点の単位の点を作り、二項評価の右単位則を全単体で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 指定された AW 単位の元は、全単体で整合する一つの点を与える。 -/
def gammaUnitPoint : 𝟙_ SSet.{u} ⟶ (truncatedDoldKanFunctor A).obj (𝟙_ (Complex A)) where
  app n := ↾fun _ => gammaUnitSimplex A n.unop
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    symm
    change (((truncatedDoldKanFunctor A).obj (𝟙_ (Complex A))).map θ)
      (normalizedSimplexHomEquiv A (𝟙_ (Complex A)) n.unop
        (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n.unop))) =
      normalizedSimplexHomEquiv A (𝟙_ (Complex A)) m.unop
        (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m.unop))
    erw [← normalizedSimplexHomEquiv_naturality]
    congr 1
    exact AlexanderWhitney.cochainCounit_natural A (SSet.stdSimplex.map θ.unop)

/-- 同じ単位の点を第二変数へ入れると、指定した右単位子そのものを得る。 -/
lemma gammaPair_right_unit_point (K : Complex A) :
    (((truncatedDoldKanFunctor A).obj K) ◁ gammaUnitPoint A) ≫
      gammaPair A K (𝟙_ (Complex A)) ≫ (truncatedDoldKanFunctor A).map (ρ_ K).hom =
    (ρ_ ((truncatedDoldKanFunctor A).obj K)).hom := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact gammaPair_right_unit A K n.unop x.1

end SerrePositivity.EInfinity.PowerOperation
