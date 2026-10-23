module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftLiftSpace

/-!
概要：任意の coherent な空間値図式の変換を unstraightening の底上の射へ移す。
方針：pointed space の射影に沿って、始点の全空間をパラメーターとする prism を持ち上げる。
規約：変換を Δ¹ ⊗ B からの射で表示し、底 B は任意。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の変換への作用とその選択空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coherent な変換の持ち上げで固定する始点と底の prism の図式。
方針：始点の pointed space 成分と、元の射影を変換に前合成した族を組み合わせる。
規約：始点条件だけを入力に要求する。
使われ方：Kerodon Lemma 5.2.2.13、coherent な変換の持ち上げの選択空間。 -/
noncomputable def leftUnstraighteningTransformationSource
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    leftUnstraightening F ⟶ relativeEdgeSourceTarget pointedSpaceProjection :=
  pullback.lift (pullback.fst pointedSpaceProjection F)
    (curry ((Δ[1] ◁ leftUnstraighteningProjection F) ≫ H)) (by
      rw [curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_naturality,
        Category.assoc, h₀]
      exact pullback.condition)

/-- 概要：coherent な変換の unstraightening の持ち上げの選択空間。
方針：相対始点評価の固定した図式上の fiber を取る。
規約：零単体は始点と底の prism を厳密に保つ持ち上げ。
使われ方：Kerodon Lemma 5.2.2.13、変換への作用の全高次の選択。 -/
noncomputable def leftUnstraighteningTransformationChoiceSpace
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) : SSet.{u + 1} :=
  relativeEdgeLiftSpace pointedSpaceProjection (leftUnstraighteningTransformationSource F H h₀)

/-- 概要：coherent な変換の unstraightening の持ち上げの選択空間は可縮な Kan 複体。
方針：pointed space の射影の left fibration 性と一般の相対持ち上げ空間の可縮性を使う。
規約：底の quasicategory 性や strict な係数図式を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6、変換の持ち上げの高次の一意性。 -/
lemma leftUnstraighteningTransformationChoiceSpace_isContractibleKan
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    IsContractibleKan (leftUnstraighteningTransformationChoiceSpace F H h₀) :=
  relativeEdgeLiftSpace_isContractibleKan pointedSpaceProjection _

/-- 概要：coherent な変換は unstraightening の間の底上の射と、その pointed な持ち上げを持つ。
方針：始点から prism を持ち上げ、終点を標的の引き戻しへ入れる。
規約：変換・始点・底を厳密に固定する。射の選択の自然性はこの存在命題に含めない。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の変換への作用。 -/
lemma exists_leftUnstraighteningTransformation
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    ∃ (f : leftUnstraightening F ⟶ leftUnstraightening G)
      (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u}),
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F ∧
      prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F ∧
      prismEndpoint 1 _ ≫ W = f ≫ pullback.fst pointedSpaceProjection G ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H := by
  let p := leftUnstraighteningProjection F
  let b := (Δ[1] ◁ p) ≫ H
  have hb : pullback.fst pointedSpaceProjection F ≫ pointedSpaceProjection =
      prismEndpoint 0 _ ≫ b := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀]
    exact pullback.condition
  obtain ⟨W, hW₀, hWp⟩ := leftFibration_lift_prism pointedSpaceProjection
    (pullback.fst pointedSpaceProjection F) b hb
  have ht : (prismEndpoint 1 _ ≫ W) ≫ pointedSpaceProjection = p ≫ G := by
    rw [Category.assoc, hWp]
    change prismEndpoint 1 _ ≫ ((Δ[1] ◁ p) ≫ H) = _
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁]
  let f : leftUnstraightening F ⟶ leftUnstraightening G :=
    pullback.lift (prismEndpoint 1 _ ≫ W) p ht
  exact ⟨f, W, pullback.lift_snd _ _ _, hW₀, (pullback.lift_fst _ _ _).symm, hWp⟩

end SerrePositivity.InfinityCategories
