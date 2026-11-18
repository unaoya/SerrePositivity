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
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 指定された AW 単位の元は、全単体で整合する一つの点を与える。 -/
def gammaUnitPoint : 𝟙_ SSet.{u} ⟶ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (𝟙_ (Complex A)) where
  app n := ↾fun _ => gammaUnitSimplex A n.unop
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    symm
    change (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (𝟙_ (Complex A))).map θ)
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (𝟙_ (Complex A)) n.unop
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n.unop))) =
      _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (𝟙_ (Complex A)) m.unop
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m.unop))
    erw [← _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_naturality]
    congr 1
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural A (SSet.stdSimplex.map θ.unop)

/-- 同じ単位の点を第二変数へ入れると、指定した右単位子そのものを得る。 -/
lemma gammaPair_right_unit_point (K : Complex A) :
    (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj K) ◁ gammaUnitPoint A) ≫
      gammaPair A K (𝟙_ (Complex A)) ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (ρ_ K).hom =
    (ρ_ ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj K)).hom := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact gammaPair_right_unit A K n.unop x.1

end SerrePositivity.EInfinity.PowerOperation
