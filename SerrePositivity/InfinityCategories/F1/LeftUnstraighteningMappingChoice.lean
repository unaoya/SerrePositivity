module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorCurryHom

/-!
概要：coherent な変換の写像空間の unstraightening 比較を、普遍的な持ち上げの任意の選択から作り比較する。
方針：可縮な相対延長の空間で終点の族を比較し、相対 curry によって比較射の関手同型へ移す。
規約：最初の図式と底の族を厳密に固定する。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射の選択からの独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：普遍的な変換の族を元の全空間へ引き戻した底の終点を計算する。
方針：prism の頂点の底変換の計算と、族の終点の固定条件を使う。
規約：持ち上げの選択には依存しない底の等式。
使われ方：Kerodon Corollary 5.6.0.6、任意の持ち上げの終点を標的の unstraightening へ入れる。 -/
lemma leftUnstraighteningMappingChoice_endpoint_base {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      (((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) =
      (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningProjection F) ≫ G := by
  rw [← Category.assoc, simplexPrismVertex_parameterizedBaseChange,
    leftUnstraighteningTransformationFamily_one, whiskerRight_fst_assoc, Category.assoc]

/-- 概要：普遍的な変換の任意の持ち上げの終点から、底上の射の族を作る。
方針：終点の pointed space 成分と元の射影を標的の引き戻しへ組み合わせる。
規約：底上の可換性も部分型に記録する。
使われ方：Kerodon Corollary 5.6.0.6、持ち上げの選択から写像空間の比較を構成する。 -/
noncomputable def leftUnstraighteningMappingFamilyOfLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) :
    {g : leftUnstraightening F ⊗ leftUnstraighteningTransformationSpace F G ⟶ leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningProjection F} :=
  ⟨pullback.lift
    ((simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫ W)
    (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningProjection F) (by
        rw [Category.assoc, hWp]
        exact leftUnstraighteningMappingChoice_endpoint_base F G), pullback.lift_snd _ _ _⟩

/-- 概要：普遍的な変換の任意の持ち上げから、相対写像空間への比較射を作る。
方針：終点の底上の族を相対 curry する。
規約：この定義の型には始点の固定条件は不要だが、選択の比較では共通の始点を要求する。
使われ方：Kerodon Corollary 5.6.0.6、比較射の持ち上げの選択を明示する API。 -/
noncomputable def leftUnstraighteningMappingSpaceMapOfLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) :
    leftUnstraighteningTransformationSpace F G ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) :=
  relativeFunctorCurry (leftUnstraighteningMappingFamilyOfLift F G W hWp).val
    (leftUnstraighteningMappingFamilyOfLift F G W hWp).property

/-- 概要：同じ初期条件を持つ二つの普遍的な持ち上げから作った写像空間の比較射は関手同型。
方針：相対延長の可縮な空間で二つの終点の族を比較し、相対 curry の豊穣作用で写す。
規約：同型は変換の空間全体から相対写像空間への二つの射の間で取る。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射の選択独立性。 -/
noncomputable def leftUnstraighteningMappingSpaceMapOfLift_iso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W W' : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hWp' : W' ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hW₀ : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G))
    (hW₀' : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W' =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G)) :
    FunctorIso (leftUnstraighteningMappingSpaceMapOfLift F G W hWp)
      (leftUnstraighteningMappingSpaceMapOfLift F G W' hWp') := by
  let g := leftUnstraighteningMappingFamilyOfLift F G W hWp
  let g' := leftUnstraighteningMappingFamilyOfLift F G W' hWp'
  let e := relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection
    (((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G)
    ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G)
    (leftAnodyneExtensions_whiskerRight _
      (simplexPrismFirstVertex_leftAnodyne 1 (leftUnstraightening F)) _)
    (leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G))
    (leftUnstraighteningParameterizedSimplexStart_projection F 1 _
      (leftUnstraighteningTransformationFamily_zero F G))
    (simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G)
    G (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningProjection F) (leftUnstraighteningMappingChoice_endpoint_base F G)
    W W' hWp hWp' hW₀ hW₀' g.val g'.val g.property g'.property
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm
  exact relativeFunctorCurryIso (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
    g.val g'.val g.property g'.property e

/-- 概要：既存の写像空間の比較射は、選択した普遍的な持ち上げから作る一般の構成に一致する。
方針：終点の引き戻しへの持ち上げと相対 curry の定義を比較する。
規約：可換性の証明は証明無関係性で同定する。
使われ方：Kerodon Corollary 5.6.0.6、選択独立性を既存の比較射へ適用する。 -/
lemma leftUnstraighteningMappingSpaceMap_eq_ofLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingSpaceMap F G =
      leftUnstraighteningMappingSpaceMapOfLift F G (leftUnstraighteningTransformationFamilyLift F G)
        (leftUnstraighteningTransformationFamilyLift_projection F G) := rfl

/-- 概要：選択済みの写像空間の比較射は、同じ初期条件を満たす任意の普遍的な持ち上げからの比較射と関手同型。
方針：選択済みの持ち上げと任意の持ち上げに、可縮な相対延長の終点の比較を適用する。
規約：始点と底の普遍的な変換の族は厳密に固定する。
使われ方：Kerodon Corollary 5.6.0.6、同値性の証明で普遍的な持ち上げを便利な選択へ変更する。 -/
noncomputable def leftUnstraighteningMappingSpaceMap_iso_ofLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hW₀ : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G)) :
    FunctorIso (leftUnstraighteningMappingSpaceMap F G)
      (leftUnstraighteningMappingSpaceMapOfLift F G W hWp) :=
  leftUnstraighteningMappingSpaceMapOfLift_iso F G
    (leftUnstraighteningTransformationFamilyLift F G) W
    (leftUnstraighteningTransformationFamilyLift_projection F G) hWp
    (leftUnstraighteningTransformationFamilyLift_zero F G) hW₀

end SerrePositivity.InfinityCategories
