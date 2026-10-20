module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomotopyConstant
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootTotalInitial

/-!
概要：時間零の端面から元の左三角形への比較を、同じ初期 Hom 空間へ移す。
方針：同じ長辺と初期頂点で円柱を fiber に戻し、元の三角形族へ端点を同定する。
規約：raw な制限・評価・底を保持する。使われ方：三比較の同じ固定終点空間での合成。
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
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "hW" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "a" => specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y
local notation "b" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "ha" => specifiedCoconeRootVerticalStartFamily_fixed hp p c hc dB dC y
local notation "hb" => specifiedCoconeLeftRootTotalFamily_fixed hp p c hc dB dC y
local notation "K" => specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y
local notation "hK" => specifiedCoconeRootVerticalStartComparison_fixed hp p c hc dB dC y
local notation "G" => initialDiagramHomFamilyHomotopy q c W (stdSimplex.δ (1 : Fin 2))
  hW y a b ha hb K hK
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の時間零の端面の、同じ固定終点の初期 Hom 族。 -/
def specifiedCoconeRootStartInitialFamily : T ⟶ leftFibrationInitialTotal q c y :=
  initialDiagramHomFamily q c W (stdSimplex.δ (1 : Fin 2)) hW y a ha

/-- 元の左三角形の初期 Hom 族へ至る、同じ時間零の比較円柱。 -/
def specifiedCoconeRootStartInitialHomotopy : SSet.Homotopy
    (specifiedCoconeRootStartInitialFamily hp p c hc dB dC y)
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) where
  h := (G).h
  h₀ := by
    exact (G).h₀
  h₁ := by
    exact (G).h₁.trans (specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 包含後は元の左比較円柱の同じ初期頂点制限である。 -/
lemma specifiedCoconeRootStartInitialHomotopy_ι :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        vertexFiberι (sliceUnderProjection (v) ≫ q) y =
      (K).h ≫ normalizedCoconeRestriction W (stdSimplex.δ (1 : Fin 2)) hW :=
  initialDiagramHomFamilyHomotopy_ι q c W (stdSimplex.δ (1 : Fin 2))
    hW y a b ha hb K hK

/-- 元の左三角形の可変終点評価を全時刻固定する。 -/
lemma specifiedCoconeRootStartInitialHomotopy_evaluation :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialEvaluation q c y := by
  have he : (K).h ≫ sliceUnderProjection W = fst T Δ[1] ≫ b ≫ sliceUnderProjection W := by
    simpa only [specifiedCoconeLeftRootTotalFamily, Category.assoc,
      sliceUnderRestrict_projection] using
      (specifiedCoconeRootVerticalStartComparison_projection hp p c hc dB dC y)
  have h := initialDiagramHomFamilyHomotopy_evaluation_constant q c W
    (stdSimplex.δ (1 : Fin 2)) hW y a b ha hb K hK he
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    leftFibrationInitialEvaluation q c y)
      (specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y))

/-- 元の左三角形の初期 Hom の底も、全時刻固定する。 -/
lemma specifiedCoconeRootStartInitialHomotopy_base :
    (specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialProjection q c y =
      fst T Δ[1] ≫ specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection q c y := by
  have h := initialDiagramHomFamilyHomotopy_base_constant q c W (stdSimplex.δ (1 : Fin 2))
    hW y a b ha hb K hK (specifiedCoconeRootVerticalStartComparison_base hp p c hc dB dC y)
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    leftFibrationInitialProjection q c y)
      (specifiedCoconeLeftRootTotalFamily_initial hp p c hc dB dC y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
