module

public import SerrePositivity.InfinityCategories.F1.SmallCoherentFamilyRecovery
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingChoice
public import SerrePositivity.InfinityCategories.F1.TransportPrismLiftSpace
public import SerrePositivity.InfinityCategories.F1.FunctorParameterizedPrismNaturality

/-!
概要：任意のパラメーター族の pointed な prism を実際の写像空間比較と結ぶ。
方針：普遍的な持ち上げを制限し共通の始点と底を保つ延長空間で比較する。
規約：全パラメーターでの関手同型を与える。
使われ方：復元した族が比較射の右逆を与えることの検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：普遍的な変換のパラメーター制限は指定した変換の族の評価。
方針：prism のパラメーター自然性と区間模型の uncurry を使う。
規約：パラメーターは任意。
使われ方：任意の族の底を普遍的な lift の底と同一視する。 -/
lemma leftUnstraighteningTransformationFamily_parameter {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    ((Δ[1] ⊗ B) ◁ t) ≫ leftUnstraighteningTransformationFamily F G =
      functorParameterizedPrism (intervalMappingUncurry t) := by
  rw [leftUnstraighteningTransformationFamily, ← functorParameterizedPrism_parameter,
    ← intervalMappingUncurry_precomp, Category.comp_id]

/-- 概要：pointed な prism の終点の族は写像空間比較の像と関手同型。
方針：普遍的な lift の制限と指定した prism を同じ始点・底の延長空間で比較する。
規約：底・パラメーターの小ささを要求しない。
使われ方：coherent な族の復元と既存の比較射の全体での整合性。 -/
def unstraighteningFamilyComparisonIso {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hw₀ : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F)
    (hw₁ : (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W =
      f ≫ pullback.fst pointedSpaceProjection G)
    (hwp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
      functorParameterizedPrism (intervalMappingUncurry t)) :
    FunctorIso (t ≫ leftUnstraighteningMappingSpaceMap F G) (relativeFunctorCurry f hf) := by
  let E := leftUnstraightening F
  let T := leftUnstraighteningTransformationSpace F G
  let p := leftUnstraighteningProjection F
  let Z := ((Δ[1] ⊗ E) ◁ t) ≫ leftUnstraighteningTransformationFamilyLift F G
  let b := ((Δ[1] ◁ p) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t)
  have hz : Z ≫ pointedSpaceProjection = b := by
    dsimp only [Z, b]
    rw [Category.assoc, leftUnstraighteningTransformationFamilyLift_projection,
      ← Category.assoc]
    have hn : ((Δ[1] ⊗ E) ◁ t) ≫ ((Δ[1] ◁ p) ▷ T) =
        ((Δ[1] ◁ p) ▷ K) ≫ ((Δ[1] ⊗ B) ◁ t) := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc, leftUnstraighteningTransformationFamily_parameter]
  have hz₀ : (prismEndpoint 0 E ▷ K) ≫ Z =
      fst E K ≫ pullback.fst pointedSpaceProjection F := by
    dsimp only [Z]
    rw [← Category.assoc, prismEndpoint_parameter_naturality, Category.assoc]
    change (E ◁ t) ≫ ((simplexPrismVertex 1 0 E ▷ T) ≫ _) = _
    rw [leftUnstraighteningTransformationFamilyLift_start, ← Category.assoc, whiskerLeft_fst]
  let g := relativeFunctorUncurry (t ≫ leftUnstraighteningMappingSpaceMap F G)
  have hg := relativeFunctorUncurry_projection (t ≫ leftUnstraighteningMappingSpaceMap F G)
  have hz₁ : (prismEndpoint 1 E ▷ K) ≫ Z = g ≫ pullback.fst pointedSpaceProjection G := by
    dsimp only [Z, g]
    rw [relativeFunctorUncurry_naturality, Category.assoc,
      leftUnstraighteningMappingSpaceMap_pointed, ← Category.assoc,
      prismEndpoint_parameter_naturality]
    rfl
  have hv : (fst E K ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection =
      (prismEndpoint 0 E ▷ K) ≫ b := by
    rw [← hw₀, Category.assoc, hwp]
  have hj : (prismEndpoint 1 E ▷ K) ≫ b = (fst E K ≫ p) ≫ G := by
    dsimp only [b, p, E]
    rw [← hwp, ← Category.assoc, hw₁, Category.assoc, pullback.condition,
      ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ G) hf
  let η := relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection b
    (prismEndpoint 0 E ▷ K)
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
    (fst E K ≫ pullback.fst pointedSpaceProjection F) hv
    (prismEndpoint 1 E ▷ K) G (fst E K ≫ p) hj
    Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁
  have e := relativeFunctorCurryIso (leftUnstraighteningProjection G) p g f hg hf η
  have hc : relativeFunctorCurry g hg = t ≫ leftUnstraighteningMappingSpaceMap F G := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G) p
    exact relativeFunctorUncurry_curry g hg
  rw [hc] at e
  exact e

end SerrePositivity.InfinityCategories
