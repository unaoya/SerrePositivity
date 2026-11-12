module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionCurryWitnessRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningSourceFamilyComparison

/-!
概要：F1 の始域付き unstraightening 比較から終点表示の正規化を外す。
方針：同じ普遍 prism と指定 prism の比較を保ち、curry 始点の等式移送を HEq へ移す。
規約：比較同型を選び直さない。使われ方：元の三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
  (i : E ⟶ leftUnstraightening F) (hi : i ≫ leftUnstraighteningProjection F = p)
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)
  (f : E ⊗ K ⟶ leftUnstraightening G)
  (hf : f ≫ leftUnstraighteningProjection G = fst E K ≫ p)
  (W : (Δ[1] ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hw₀ : (prismEndpoint 0 E ▷ K) ≫ W = fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F)
  (hw₁ : (prismEndpoint 1 E ▷ K) ≫ W = f ≫ pullback.fst pointedSpaceProjection G)
  (hwp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ p) ▷ K) ≫
    functorParameterizedPrism (intervalMappingUncurry t))
local notation "Z" => (((Δ[1] ◁ i) ⊗ₘ t) ≫ leftUnstraighteningTransformationFamilyLift F G)
local notation "d" => ((Δ[1] ◁ p) ▷ K) ≫
  functorParameterizedPrism (intervalMappingUncurry t)
local notation "v" => fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F
local notation "g" => (i ⊗ₘ t) ≫ relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G)

/-- 始域付き比較で正規化した curry 始点は元の前合成された比較射そのもの。 -/
lemma unstraighteningSourceComparison_curry_source
    (hg : g ≫ leftUnstraighteningProjection G = fst E K ≫ p) :
    relativeFunctorCurry g hg = (t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection F)) i hi) := by
  apply relativeFunctorUncurry_injective
  rw [relativeFunctorUncurry_curry]
  have h := relativeFunctorOverPre_uncurry (leftUnstraighteningProjection G)
    (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection F)) i hi)
    (t ≫ leftUnstraighteningMappingSpaceMap F G)
  rw [relativeFunctorUncurry_naturality] at h
  exact (h.trans (by apply SSet.hom_ext; intro n; rfl)).symm

/-- 実際の始域付き比較は同じ二 prism の終点比較の curry の等式移送。 -/
lemma unstraighteningSourceComparisonIso_heq_endpoint
    (hz : Z ≫ pointedSpaceProjection = d) (hz₀ : (prismEndpoint 0 E ▷ K) ≫ Z = v)
    (hg : g ≫ leftUnstraighteningProjection G = fst E K ≫ p)
    (hz₁ : (prismEndpoint 1 E ▷ K) ≫ Z = g ≫ pullback.fst pointedSpaceProjection G)
    (hv : v ≫ pointedSpaceProjection = (prismEndpoint 0 E ▷ K) ≫ d)
    (hj : (prismEndpoint 1 E ▷ K) ≫ d = (fst E K ≫ p) ≫ G) :
    HEq (unstraighteningSourceFamilyComparisonIso F G p i hi t f hf W hw₀ hw₁ hwp)
      (relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection d
        (prismEndpoint 0 E ▷ K)
        (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
        v hv (prismEndpoint 1 E ▷ K) G p hj
        Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁) := by
  unfold unstraighteningSourceFamilyComparisonIso
  dsimp only
  have hcast {α β : Sort (u + 2)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

end SerrePositivity.InfinityCategories.F2
