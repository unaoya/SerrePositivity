module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFunctorTheorem

/-!
概要：e1 の保存関手圏の頂点を d の随伴関手定理へ接続する。
方針：全部分関手圏の元の頂点を読み、左右の随伴存在判定を適用する。
規約：関手圏の高次単体は変更せず、随伴の存在を追加入力にしない。
使われ方：Pr の双対性を構成する際の頂点上の対応。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：Pr^L の関手圏の頂点を元の関手へ戻す。
方針：全部分複体の包含と関手頂点の全単射を使う。
規約：元の始域と標的を保持する。
使われ方：選んだ右随伴の左側の関手。 -/
def leftVertexFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : C.obj ⟶ D.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v.val

/-- 概要：Pr^R の関手圏の頂点を元の関手へ戻す。
方針：元の全部分関手圏の頂点の値を読む。
規約：小極限保存と accessibility は頂点条件から回収する。
使われ方：選んだ左随伴の右側の関手。 -/
def rightVertexFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D _⦋0⦌) : C.obj ⟶ D.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm v.val

/-- 概要：Pr^L の元の関手圏の各頂点は右随伴を持つ。
方針：頂点の小余極限保存に d の存在判定を適用する。
規約：随伴を持つことを頂点の定義に追加しない。
使われ方：右随伴の選択。 -/
lemma leftVertex_exists_rightAdjoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    ∃ R : D.obj ⟶ C.obj, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (leftVertexFunctor v) R) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits C.isPresentable D.isPresentable _).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)

/-- 概要：Pr^R の元の関手圏の各頂点は左随伴を持つ。
方針：二つの頂点条件に d の存在判定を適用する。
規約：指定された元の右関手に対する随伴。
使われ方：左随伴の選択。 -/
lemma rightVertex_exists_leftAdjoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D _⦋0⦌) :
    ∃ L : D.obj ⟶ C.obj, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (rightVertexFunctor v)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits D.isPresentable C.isPresentable _).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)

/-- 概要：Pr^L 頂点の右随伴を一つ選ぶ。
方針：存在判定の証拠から選択する。
規約：全関手圏上の単体写像をこの選択だけからは主張しない。
使われ方：随伴対応の頂点の値。 -/
def chosenRightAdjoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : D.obj ⟶ C.obj :=
  Classical.choose (leftVertex_exists_rightAdjoint v)

/-- 概要：選んだ右関手との元の全随伴。
方針：選択の存在証明を取り出す。
規約：h Fun 内の単位・余単位と三角恒等式を持つ。
使われ方：保存性と随伴の一意性の回収。 -/
def chosenRightAdjunction {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (leftVertexFunctor v) (chosenRightAdjoint v) :=
  Classical.choice (Classical.choose_spec (leftVertex_exists_rightAdjoint v))

/-- 概要：Pr^R 頂点の左随伴を一つ選ぶ。
方針：d の存在判定の証拠から選択する。
規約：高次の自然性は別に構成する必要がある。
使われ方：逆対応の頂点の値。 -/
def chosenLeftAdjoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D _⦋0⦌) : D.obj ⟶ C.obj :=
  Classical.choose (rightVertex_exists_leftAdjoint v)

/-- 概要：選んだ左関手との元の全随伴。
方針：左随伴の存在証明を取り出す。
規約：右側は元の Pr^R 頂点の関手のまま。
使われ方：逆対応の保存性と一意性。 -/
def chosenLeftAdjunction {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (chosenLeftAdjoint v) (rightVertexFunctor v) :=
  Classical.choice (Classical.choose_spec (rightVertex_exists_leftAdjoint v))

/-- 概要：選んだ右随伴は Pr^R の保存条件を満たす。
方針：d の判定の必要方向を元の随伴に適用する。
規約：accessibility の濃度を別途仮定しない。
使われ方：右側の関手圏への所属。 -/
lemma chosenRightAdjoint_condition {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableFunctorCondition false (chosenRightAdjoint v) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits C.isPresentable D.isPresentable _).mp
    ⟨_, ⟨chosenRightAdjunction v⟩⟩

/-- 概要：選んだ左随伴は Pr^L の保存条件を満たす。
方針：随伴関手定理の必要方向を適用する。
規約：指定された全小余極限を保存する。
使われ方：左側の関手圏への所属。 -/
lemma chosenLeftAdjoint_condition {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableFunctorCondition true (chosenLeftAdjoint v) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits D.isPresentable C.isPresentable _).mp
    ⟨_, ⟨chosenLeftAdjunction v⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
