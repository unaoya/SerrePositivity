module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootBaseComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceDiagramChangeRestriction

/-!
概要：既存の左右の底の円柱を、同じ実際の右長辺の射影上へ移す。
方針：射影の厳密な等式で表示を変え、元の二族の底と終端固定の式を照合する。
規約：底の比較円柱を選び直さない。使われ方：右長辺上の相対 coslice 持ち上げ。
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
local notation "V" => tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "a" => specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y
local notation "b" => specifiedCoconeRightRootTotalFamily hp p c hc dB dC y
local notation "L" => specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y
local notation "R" => specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y
local notation "H" => specifiedCoconeRootBaseFamilyComparison hp p c hc dB dC y
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "I" => eqToIso (congrArg sliceUnder hV)
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の左右の底の比較を、同じ右長辺の射影上の二族の間へ移す。 -/
def specifiedCoconeRightRootBaseComparison : SSet.Homotopy
    (a ≫ sliceUnderPostcomp V q) (b ≫ sliceUnderPostcomp V q) where
  h := (H).h ≫ (I).inv
  h₀ := by
    change SSet.ι₀ ≫ ((H).h ≫ (I).inv) = a ≫ sliceUnderPostcomp V q
    rw [← Category.assoc SSet.ι₀ (H).h (I).inv, (H).h₀]
    apply (cancel_mono (I).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (specifiedCoconeRootVerticalEndFamily_base hp p c hc dB dC y).symm
  h₁ := by
    change SSet.ι₁ ≫ ((H).h ≫ (I).inv) = b ≫ sliceUnderPostcomp V q
    rw [← Category.assoc SSet.ι₁ (H).h (I).inv, (H).h₁]
    apply (cancel_mono (I).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (specifiedCoconeRightRootTotalFamily_base hp p c hc dB dC y).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- raw な底の円柱は、元の比較円柱に厳密な表示変更を後合成したもの。 -/
lemma specifiedCoconeRightRootBaseComparison_raw :
    (specifiedCoconeRightRootBaseComparison hp p c hc dB dC y).h = (H).h ≫ (I).inv := rfl

/-- 上の元の右族の終端係数と、底の円柱は全時刻で整合する。 -/
lemma specifiedCoconeRightRootBaseComparison_terminal :
    (specifiedCoconeRightRootBaseComparison hp p c hc dB dC y).h ≫
        sliceUnderRestrict (V ≫ q) (stdSimplex.δ (0 : Fin 2)) =
      fst T Δ[1] ≫ b ≫ sliceUnderRestrict V (stdSimplex.δ (0 : Fin 2)) ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ V) q := by
  have h := cosliceDiagramChange_restriction_eq (hV).symm (stdSimplex.δ (0 : Fin 2))
    (H).h (fst T Δ[1] ≫ R)
    (specifiedCoconeRootBaseFamilyComparison_terminal hp p c hc dB dC y)
  have hR : R ≫ (I).inv = b ≫ sliceUnderPostcomp V q := by
    apply (cancel_mono (I).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (specifiedCoconeRightRootTotalFamily_base hp p c hc dB dC y).symm
  change ((H).h ≫ (I).inv) ≫ sliceUnderRestrict (V ≫ q) (stdSimplex.δ (0 : Fin 2)) =
    ((fst T Δ[1] ≫ R) ≫ (I).inv) ≫ sliceUnderRestrict (V ≫ q)
      (stdSimplex.δ (0 : Fin 2)) at h
  rw [Category.assoc (fst T Δ[1]) R (I).inv, hR] at h
  simpa only [specifiedCoconeRightRootBaseComparison, Category.assoc,
    sliceUnderRestrict_postcomp] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
