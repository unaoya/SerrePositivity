module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterValueEquivalences
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNuComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletedLandTamme
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：元実外周の resolved 商辺を、同じ LT 外周の完備化後射影へ全比較する。
方針：同じ cell 増大屋根・native lax 射影比較・実完備化射を全関手同型で貼る。
規約：完備化後の射を厳密局所化と扱わず、元射影を保持する。
使われ方：実外周の指定商境界と全二胞体比較の第二側面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "B" => DGOdotGluing R d
local notation "P" => dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "E" => dgOdotMilnorCellMiddleNativeValueEquivalence R d
local notation "b" => dgOdotMilnorOuterMiddleValueEquivalence R d
local notation "q" => dgOdotMilnorCellProjectionExactMap R d
local notation "κ" => dgOdotMilnorCompletion R d
local notation "ε" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (B))
local instance outerProjection_middle_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d

/-- 概要：元 LT 外周の同じ完備化後射影。
方針：同じ構成済み列から回収する。規約：元射影を保持。
使われ方：元実外周の商境界との照合。 -/
def dgOdotMilnorOuterCompletedProjection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorLaxCategory R d)
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) :=
  (dgOdotMilnorCompletedLaxQuotient R d h).sequence.projection
local notation "r" => dgOdotMilnorOuterCompletedProjection R d h

/-- 概要：元 LT 外周の完備化後射影は同じ lax 射影と実 c の合成。
方針：元構成の射を回収する。規約：同じ c を保持。
使われ方：元 cell 商辺との全比較の型照合。 -/
lemma dgOdotMilnorOuterProjection_hom :
    (r).hom = (dgOdotMilnorLaxProjection R d).hom ≫ (κ).hom := rfl

/-- 概要：元実外周の商辺は同じ中央比較と元 LT 完備化後射影で全自然に可換。
方針：元 cell 増大屋根・元 native lax 射影比較・同じ実 c の自然性を貼る。
規約：元 resolved 射影と完備化を保持。使われ方：指定商辺の実全比較。 -/
def dgOdotMilnorOuterProjectionComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((b).hom ≫ (r).hom) (q).hom := by
  apply ((E).isQCatEquivalence.precompose
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E).hom ≫ ((b).hom ≫ (r).hom)) ((E).hom ≫ (q).hom)
  have h₁ := (dgOdotMilnorOuterMiddleValueEquivalence_native R d).postcomp (r).hom
  have h₂ := (dgOdotMilnorCompletedProjectionComparison R d (κ)).precomp (ε)
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientRoofIso R (B) (P)).postcomp (κ).hom
  have h₄ := (dgOdotMilnorCellProjectionNuComparison R d).symm
  have e₁ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₁ (Category.assoc _ _ _) (Category.assoc _ _ _)
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((ε) ≫ ((dgOdotMilnorNativeLaxEquivalence R d).hom ≫ (r).hom))
      ((ε) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom ≫ (κ).hom)) := by
    rw [dgOdotMilnorOuterProjection_hom]
    exact h₂
  have e₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((ε) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom ≫ (κ).hom))
      ((dgOdotMilnorCellNativeProjection R d).hom ≫ (κ).hom) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((ε) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R (B) (P) ≫ (κ).hom))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R (B) (P) ≫ (κ).hom)
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₃ (Category.assoc _ _ _) rfl
  exact e₁.trans (e₂.trans (e₃.trans h₄))
end SerrePositivity.KST.SConstruction
