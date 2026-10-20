module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootFamilyTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightRootTotalTip

/-!
概要：既存の左右の根辺比較円柱を、固定頂点 fiber から底の coslice の全族へ戻す。
方針：同じ比較円柱に fiber 包含を後合成し、元の全族の両端と終端固定を計算する。
規約：元の円柱を選び直さない。使われ方：右長辺上の指定した底ホモトピーの持ち上げ。
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
local notation "e" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "L" => specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y
local notation "R" => specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y
local notation "H" => specifiedCoconeRootFamilyComparison hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の同じ fiber 比較を包含した、底の余錐空間の実際の比較円柱。 -/
def specifiedCoconeRootBaseFamilyComparison : SSet.Homotopy L R where
  h := (H).h ≫ vertexFiberι (sliceUnderProjection e) y
  h₀ := by
    change SSet.ι₀ ≫ ((H).h ≫ vertexFiberι (sliceUnderProjection e) y) = L
    rw [← Category.assoc, (H).h₀, specifiedCoconeLeftRootBaseEdgeFiberFamily,
      vertexFiberLift_ι]
  h₁ := by
    change SSet.ι₁ ≫ ((H).h ≫ vertexFiberι (sliceUnderProjection e) y) = R
    rw [← Category.assoc, (H).h₁, specifiedCoconeRootBaseEdgeFiberFamily,
      vertexFiberLift_ι]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- raw な底の円柱は、元の同じ fiber 比較円柱の包含そのもの。 -/
lemma specifiedCoconeRootBaseFamilyComparison_raw :
    (specifiedCoconeRootBaseFamilyComparison hp p c hc dB dC y).h =
      (H).h ≫ vertexFiberι (sliceUnderProjection e) y := rfl

/-- 底の全族の比較も、元の終端係数を全時刻固定する。 -/
lemma specifiedCoconeRootBaseFamilyComparison_terminal :
    (specifiedCoconeRootBaseFamilyComparison hp p c hc dB dC y).h ≫
        sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) =
      fst T Δ[1] ≫ R ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) := by
  have ht := specifiedCoconeRootFamilyComparison_target hp p c hc dB dC y
  rw [specifiedCoconeRootFamilies_target hp p c hc dB dC y] at ht
  have h := congrArg
    (fun k ↦ k ≫ vertexFiberι
      (sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) y)
    ht
  simp only [cosliceRestrictionFiberMap, Category.assoc, vertexFiberMap_ι] at h
  simp only [specifiedCoconeRootBaseEdgeFiberFamily, ← Category.assoc,
    vertexFiberLift_ι] at h
  simpa only [specifiedCoconeRootBaseFamilyComparison, Category.assoc] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
