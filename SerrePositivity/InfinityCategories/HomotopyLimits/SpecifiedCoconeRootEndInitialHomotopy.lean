module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootStartInitialHomotopy
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalEndComparison

/-!
概要：時間一の端面から元の右四面体への比較を、同じ初期 Hom 空間へ移す。
方針：実際の右長辺の初期頂点に同じ円柱を制限し、元の四面体族へ端点を同定する。
規約：元の円柱の底への像を保持する。使われ方：三つの比較の固定終点空間での合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder (f ≫ (i ≫ p)))) c
local notation "V" => tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC
local notation "a" => specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y
local notation "b" => specifiedCoconeRightRootTotalFamily hp p c hc dB dC y
local notation "ha" => specifiedCoconeRootVerticalEndFamily_fixed hp p c hc dB dC y
local notation "hb" => specifiedCoconeRightRootTotalFamily_fixed hp p c hc dB dC y
local notation "K" => specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y
local notation "hK" => specifiedCoconeRootVerticalEndComparison_fixed hp p c hc dB dC y
local notation "G" => initialDiagramHomFamilyHomotopy q c V (stdSimplex.δ (1 : Fin 2))
  hV y a b ha hb K hK
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の時間一の端面の、同じ固定終点の初期 Hom 族。 -/
def specifiedCoconeRootEndInitialFamily : T ⟶ leftFibrationInitialTotal q c y :=
  initialDiagramHomFamily q c V (stdSimplex.δ (1 : Fin 2)) hV y a ha

/-- 元の右四面体の初期 Hom 族へ至る、同じ時間一の比較円柱。 -/
def specifiedCoconeRootEndInitialHomotopy : SSet.Homotopy
    (specifiedCoconeRootEndInitialFamily hp p c hc dB dC y)
    (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y) where
  h := (G).h
  h₀ := by
    exact (G).h₀
  h₁ := by
    exact (G).h₁.trans (specifiedCoconeRightRootTotalFamily_initial hp p c hc dB dC y)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 包含後は元の右比較円柱の同じ初期頂点制限である。 -/
lemma specifiedCoconeRootEndInitialHomotopy_ι :
    (specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y).h ≫
        vertexFiberι (sliceUnderProjection (v) ≫ q) y =
      (K).h ≫ normalizedCoconeRestriction V (stdSimplex.δ (1 : Fin 2)) hV :=
  initialDiagramHomFamilyHomotopy_ι q c V (stdSimplex.δ (1 : Fin 2))
    hV y a b ha hb K hK

/-- 元の右四面体の可変終点評価を全時刻固定する。 -/
lemma specifiedCoconeRootEndInitialHomotopy_evaluation :
    (specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialEvaluation q c y := by
  have h := initialDiagramHomFamilyHomotopy_evaluation_constant q c V
    (stdSimplex.δ (1 : Fin 2)) hV y a b ha hb K hK
    (specifiedCoconeRootVerticalEndComparison_projection hp p c hc dB dC y)
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    leftFibrationInitialEvaluation q c y)
      (specifiedCoconeRightRootTotalFamily_initial hp p c hc dB dC y))

/-- 底の初期 Hom への像も、元の右比較円柱の同じ初期頂点制限である。 -/
lemma specifiedCoconeRootEndInitialHomotopy_base :
    (specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialProjection q c y ≫
          vertexFiberι (sliceUnderProjection (v ≫ q)) y =
      ((K).h ≫ sliceUnderPostcomp V q) ≫
        normalizedCoconeRestriction (V ≫ q) (stdSimplex.δ (1 : Fin 2))
          ((Category.assoc (stdSimplex.δ (1 : Fin 2)) V q).symm.trans
            (congrArg (fun m ↦ m ≫ q) hV)) :=
  initialDiagramHomFamilyHomotopy_base q c V (stdSimplex.δ (1 : Fin 2))
    hV y a b ha hb K hK

end
end SerrePositivity.InfinityCategories.HomotopyLimits
