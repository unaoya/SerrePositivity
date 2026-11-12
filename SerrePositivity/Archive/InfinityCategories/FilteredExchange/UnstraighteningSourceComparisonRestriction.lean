module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningSourceComparisonPresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

/-!
概要：F1 の実際の始域付き比較の成分を同じ二 prism の制限後の比較へ移す。
方針：curry 始点の正規化を外して、具体的な prism 比較の制限式を適用する。
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
variable {E B K C : SSet.{u + 1}} [Quasicategory K] (F G : B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
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

local notation "η" => unstraighteningSourceFamilyComparisonIso F G p i hi t f hf W hw₀ hw₁ hwp

/-- 始域付き比較の各点成分は同じ実 prism の制限の指定比較となる。 -/
lemma unstraighteningSourceComparisonIso_app_pre
    (hz : Z ≫ pointedSpaceProjection = d) (hz₀ : (prismEndpoint 0 E ▷ K) ≫ Z = v)
    (hg : g ≫ leftUnstraighteningProjection G = fst E K ≫ p)
    (hz₁ : (prismEndpoint 1 E ▷ K) ≫ Z = g ≫ pullback.fst pointedSpaceProjection G)
    (hv : v ≫ pointedSpaceProjection = (prismEndpoint 0 E ▷ K) ≫ d)
    (hj : (prismEndpoint 1 E ▷ K) ≫ d = (fst E K ≫ p) ≫ G)
    (l : K _⦋0⦌) (s₀ : C ⟶ E) :
    let s := s₀ ≫ lift (𝟙 E) (SSet.const l)
    let r := prismExtensionRestriction pointedSpaceProjection d v hv s
    let x := relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 E ▷ K) v hv ⟨Z, hz, hz₀⟩
    let y := relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 E ▷ K) v hv ⟨W, hwp, hw₀⟩
    HEq (VertexIso.map ((η).app l) (relativeFunctorPre (leftUnstraighteningProjection G) p s₀))
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection
          (prismParameterRestriction s ≫ d) (prismEndpoint 0 C)
          (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
          (by rw [Category.assoc, hv]; rfl)).vertexIso (r.app _ x) (r.app _ y))
        (relativeFunctorExtensionEndpoint pointedSpaceProjection (prismParameterRestriction s ≫ d)
          (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
          (prismEndpoint 1 C) G (s ≫ (fst E K ≫ p))
          (prismExtensionPullbackRestriction_endpoint d s G (fst E K ≫ p) hj))) := by
  dsimp only
  let e := relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection d
    (prismEndpoint 0 E ▷ K)
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
    v hv (prismEndpoint 1 E ▷ K) G p hj Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁
  have hc := unstraighteningSourceComparison_curry_source F G p i hi t hg
  have he := functorIso_app_heq_of_heq η e hc.symm rfl
    (unstraighteningSourceComparisonIso_heq_endpoint F G p i hi t f hf W hw₀ hw₁ hwp
      hz hz₀ hg hz₁ hv hj) l
  have hm := vertexIso_map_heq_of_heq ((η).app l) (e.app l)
    (congrArg (fun k => k.app (Opposite.op ⦋0⦌) l) hc.symm) rfl he
    (relativeFunctorPre (leftUnstraighteningProjection G) p s₀)
  exact hm.trans (prismExtensionCurryWitnessIso_restrict pointedSpaceProjection d v hv l s₀ G p hj
    Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁)

end SerrePositivity.InfinityCategories.F2
