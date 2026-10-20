module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismSquareComposition
public import SerrePositivity.InfinityCategories.F1B.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianPrismComparison

/-!
概要：元の同じ単位・左右輸送・比較正方形から、単位成分の合成式を回収。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較と一般 coherent 極限保存は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 同じ元の比較正方形から、単位成分と右輸送の合成が左輸送に一致することを導く。 -/
lemma cartesianComparison_component_comp {X Y E : SSet.{u}} [Quasicategory E]
    (F : X ⟶ Y) (G : Y ⟶ X) (i : X ⟶ E) (j : Y ⟶ E)
    (η : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (hη0 : prismEndpoint 0 X ≫ η = 𝟙 X) (hη1 : prismEndpoint 1 X ≫ η = F ≫ G)
    (HL : (Δ[1] : SSet.{u}) ⊗ X ⟶ E)
    (hL0 : prismEndpoint 0 X ≫ HL = i) (hL1 : prismEndpoint 1 X ≫ HL = F ≫ j)
    (HR : (Δ[1] : SSet.{u}) ⊗ Y ⟶ E)
    (hR0 : prismEndpoint 0 Y ≫ HR = G ≫ i) (hR1 : prismEndpoint 1 Y ≫ HR = j)
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ X) ⟶ E)
    (hηi : η ≫ i = prismEndpoint 0 _ ≫ J)
    (hJb : ((Δ[1] : SSet.{u}) ◁ ((boundary 1).ι ▷ X)) ≫ J =
      cartesianComparisonBoundary HL (((Δ[1] : SSet.{u}) ◁ F) ≫ HR))
    (hJ1 : prismEndpoint 1 _ ≫ J = HL) (x : X _⦋0⦌) :
    (hoFunctor.map i).toFunctor.map (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (homotopyOfPrism η hη0 hη1))) x) ≫
      functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (homotopyOfPrism HR hR0 hR1)))
        (F.app (Opposite.op ⦋0⦌) x) =
    functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (homotopyOfPrism HL hL0 hL1))) x := by
  let Hu := homotopyOfPrism η hη0 hη1
  let Hr := homotopyOfPrism HR hR0 hR1
  let Hl := homotopyOfPrism HL hL0 hL1
  have hzero : ((Δ[1] : SSet.{u}) ◁ prismEndpoint 0 X) ≫ J = snd Δ[1] X ≫ i := by
    rw [← intervalBoundaryEndpoint_ι 0, whiskerLeft_comp, Category.assoc, hJb,
      cartesianComparisonBoundary_zero, hL0]
  have hone : ((Δ[1] : SSet.{u}) ◁ prismEndpoint 1 X) ≫ J =
      ((Δ[1] : SSet.{u}) ◁ F) ≫ HR := by
    rw [← intervalBoundaryEndpoint_ι 1, whiskerLeft_comp, Category.assoc, hJb,
      cartesianComparisonBoundary_one]
  have h := prismSquareAt_component_comp (functorHomotopyPostcomp Hu i)
    (functorHomotopyPrecomp Hr F) Hl J hzero ?_ ?_ ?_ x
  · rw [functorHomEvaluate_homotopy_postcomp, functorHomotopyPrecomp_hom,
      functorHomEvaluate_precomp] at h
    exact h
  · exact hone
  · exact hηi.symm
  · exact hJ1

end
end SerrePositivity.InfinityCategories.HomotopyLimits
