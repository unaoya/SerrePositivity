module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningTransformation
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.LiftEndpoint

/-!
概要：coherent な変換の持ち上げの可縮な選択空間から、unstraightening 間の相対写像空間への射。
方針：持ち上げの終点を取り、引き戻しに沿う相対関手空間の同型を使う。
規約：選択間の比較は全空間内だけでなく、同じ底の上の写像空間内に置く。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の変換への作用の高次の一意性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対的な辺の lift の終点の底は指定された底の prism の終点。
方針：相対始点評価の第二射影と端点評価を計算する。
規約：p に充填性を要求しない。
使われ方：Kerodon Lemma 5.2.2.13、終点の底の図式の固定。 -/
lemma relativeEdgeEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) :
    evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ p =
      relativeEdgeSource p ≫ pullback.snd p
        (evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [relativeEdgeSource, pullback.lift_snd_assoc]
  rfl

/-- 概要：相対的な辺の lift の選択空間から、終点で固定された相対関手空間への射。
方針：終点評価で後合成し、指定された底の図式の fiber へ持ち上げる。
規約：パラメーター A は任意。
使われ方：Kerodon Lemma 5.2.2.13、選択の終点を高次の族として比較する。 -/
noncomputable def relativeEdgeLiftSpaceEndpoint {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    relativeEdgeLiftSpace p c ⟶ relativeFunctorSpace p
      (c ≫ pullback.snd p
        (evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  vertexFiberLift _ _
    (vertexFiberι ((ihom A).map (relativeEdgeSource p)) (functorVertex c) ≫
      (ihom A).map (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) (by
    rw [Category.assoc, ← Functor.map_comp, relativeEdgeEndpoint_comp, Functor.map_comp,
      ← Category.assoc, vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：coherent な変換の持ち上げの底の図式の終点は元の射影の後の標的図式。
方針：prism の端点の自然性と標的条件を使う。
規約：底の射影を厳密に固定した等式。
使われ方：Kerodon Remark 5.6.2.5、終点を unstraightening の pullback に入れる計算。 -/
lemma leftUnstraighteningTransformationSource_endpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    leftUnstraighteningTransformationSource F H h₀ ≫
      pullback.snd pointedSpaceProjection
        (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      leftUnstraighteningProjection F ≫ G := by
  rw [leftUnstraighteningTransformationSource, pullback.lift_snd_assoc,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, h₁]

/-- 概要：coherent な変換の lift の選択を、unstraightening 間の底上の相対関手へ送る。
方針：選択空間の終点を取り、標的図式に沿う引き戻しの相対関手同型の逆射へ合成する。
規約：始点と終点の底は同じ B。選択空間全体を始域にする。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の変換の選択を比較する写像。 -/
noncomputable def leftUnstraighteningTransformationEndpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    leftUnstraighteningTransformationChoiceSpace F H h₀ ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) := by
  let c := leftUnstraighteningTransformationSource F H h₀
  have e : leftUnstraighteningTransformationChoiceSpace F H h₀ ⟶
      relativeFunctorSpace pointedSpaceProjection (leftUnstraighteningProjection F ≫ G) := by
    have h := leftUnstraighteningTransformationSource_endpoint F G H h₀ h₁
    simpa only [c, h, leftUnstraighteningTransformationChoiceSpace] using
      relativeEdgeLiftSpaceEndpoint pointedSpaceProjection c
  exact e ≫ (relativeFunctorBaseChangeIso pointedSpaceProjection G
    (leftUnstraighteningProjection F)).inv

/-- 概要：coherent な変換の任意の二つの持ち上げの終点は、底上の写像空間内で同型。
方針：可縮な選択空間の二頂点の同型を終点の射で写す。
規約：底を忘れた関手の同型だけには弱めない。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の変換への作用の選択独立性。 -/
noncomputable def leftUnstraighteningTransformationEndpointIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (x y : (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌) :
    VertexIso ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ x)
      ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ y) :=
  ((leftUnstraighteningTransformationChoiceSpace_isContractibleKan F H h₀).vertexIso x y).map
    (leftUnstraighteningTransformationEndpoint F G H h₀ h₁)

end SerrePositivity.InfinityCategories
