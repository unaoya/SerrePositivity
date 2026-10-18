module

public import SerrePositivity.InfinityCategories.F1.LeftTransport
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：始点と底の辺の族を固定した left fibration の lift の可縮な選択空間。
方針：相対始点評価での後合成の、指定した図式上の fiber を取る。
規約：選択空間の零単体は図式全体の lift と同一視する。
使われ方：Kerodon Proposition 5.2.2.8、Lemma 5.2.2.13 の一意性の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した始点と底の辺の族の lift の単体集合。
方針：パラメーター A 上の後合成の射の、指定した図式 c 上の fiber を取る。
規約：A の quasicategory 性は仮定しない。
使われ方：Kerodon Lemma 5.2.2.13、transport の選択を整合的に比較する空間。 -/
noncomputable def relativeEdgeLiftSpace {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) : SSet.{u} :=
  vertexFiber ((ihom A).map (relativeEdgeSource p)) (functorVertex c)

/-- 概要：left fibration の相対的な辺の lift の選択空間は可縮な Kan 複体。
方針：trivial Kan fibration の内部 Hom とその fiber の可縮性を使う。
規約：底・全空間・パラメーターに quasicategory 性は不要。
使われ方：Kerodon Proposition 5.2.2.8、lift の全高次整合性を含む一意性。 -/
lemma relativeEdgeLiftSpace_isContractibleKan {A X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (c : A ⟶ relativeEdgeSourceTarget p) :
    IsContractibleKan (relativeEdgeLiftSpace p c) :=
  vertexFiber_isContractibleKan _ _

/-- 概要：選択空間の零単体は指定図式 c の厳密な lift と同じデータ。
方針：内部 Hom の頂点と射の同値を、後合成の fiber に制限する。
規約：この同値自体は p の fibration 性を仮定しない。
使われ方：Kerodon Lemma 5.2.2.13、可縮性と実際の lift の接続。 -/
noncomputable def relativeEdgeLiftSpaceVertexEquiv {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    {F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X // F ≫ relativeEdgeSource p = c} ≃
      (relativeEdgeLiftSpace p c) _⦋0⦌ where
  toFun F := ⟨functorVertex F.val, by
    change functorVertex (F.val ≫ relativeEdgeSource p) = PinchedHom.constant _ 0
    rw [pinchedConstant_zero, F.property]⟩
  invFun s := ⟨(functorVertexEquiv _ _).symm s.val, by
    apply functorVertex_injective
    have hs : functorVertex ((functorVertexEquiv _ _).symm s.val) = s.val :=
      (functorVertexEquiv _ _).apply_symm_apply s.val
    change ((ihom A).map (relativeEdgeSource p)).app (Opposite.op ⦋0⦌)
      (functorVertex ((functorVertexEquiv _ _).symm s.val)) = functorVertex c
    rw [hs]
    simpa only [pinchedConstant_zero] using s.property⟩
  left_inv F := Subtype.ext ((functorVertexEquiv _ _).symm_apply_apply F.val)
  right_inv s := Subtype.ext ((functorVertexEquiv _ _).apply_symm_apply s.val)

end SerrePositivity.InfinityCategories
