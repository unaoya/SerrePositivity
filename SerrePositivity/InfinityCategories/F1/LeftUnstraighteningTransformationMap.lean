module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningTransformationEndpoint
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorUnitHom

/-!
概要：coherent な図式の変換に unstraightening 間の実際の底上の射を対応させる。
方針：可縮な持ち上げの選択空間の頂点を選び、終点の相対関手を通常の射へ戻す。
規約：選んだ射の恒等・合成との高次の整合性は後続で証明する。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent 図式の変換への作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coherent な変換の持ち上げの可縮な選択空間の頂点を一つ選ぶ。
方針：可縮な Kan 複体の頂点の非空性を使う。
規約：標的条件は不要で、始点と底の変換を固定する。
使われ方：Kerodon Lemma 5.2.2.13、unstraightening の変換の非計算的な選択。 -/
noncomputable def leftUnstraighteningTransformationChoice
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌ :=
  Classical.choice (leftUnstraighteningTransformationChoiceSpace_isContractibleKan F H h₀).nonempty

/-- 概要：coherent な変換に対応する unstraightening 間の底上の射を選ぶ。
方針：選択した持ち上げの終点の相対関手頂点を、底上の射の部分型へ戻す。
規約：値は射と底上の可換性の証明を同時に持つ。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式間の変換の実際の作用。 -/
noncomputable def leftUnstraighteningTransformationMap
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F} :=
  (relativeFunctorVertexEquiv (leftUnstraighteningProjection G)
    (leftUnstraighteningProjection F)).symm
      ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _
        (leftUnstraighteningTransformationChoice F H h₀))

/-- 概要：選択した unstraightening の変換を相対関手頂点に戻すと、選択した lift の終点になる。
方針：相対関手頂点と底上の射の全単射の往復を使う。
規約：射とその可換性の証明を同時に比較する。
使われ方：Kerodon Corollary 5.6.0.6、選択した通常の射と可縮な選択空間の接続。 -/
lemma leftUnstraighteningTransformationMap_vertex
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningTransformationMap F G H h₀ h₁).val
      (leftUnstraighteningTransformationMap F G H h₀ h₁).property =
    (leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _
      (leftUnstraighteningTransformationChoice F H h₀) :=
  (relativeFunctorVertexEquiv (leftUnstraighteningProjection G)
    (leftUnstraighteningProjection F)).apply_symm_apply _

/-- 概要：選択した unstraightening の変換は任意の別の持ち上げの終点と底上の写像空間で同型。
方針：可縮な選択空間の終点の同型を、通常の射の相対頂点表示へ移す。
規約：底を保つ相対関手空間内の同型。
使われ方：Kerodon Corollary 5.6.0.6、変換への作用の選択からの独立性。 -/
noncomputable def leftUnstraighteningTransformationMapChoiceIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (x : (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F G H h₀ h₁).val
        (leftUnstraighteningTransformationMap F G H h₀ h₁).property)
      ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ x) := by
  rw [leftUnstraighteningTransformationMap_vertex]
  exact leftUnstraighteningTransformationEndpointIso F G H h₀ h₁
    (leftUnstraighteningTransformationChoice F H h₀) x

end SerrePositivity.InfinityCategories
