module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoproductFunctorIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace

/-!
概要：同じ底を保つ fiber ごとの関手の形状制限。
方針：内部 Hom の前合成を、定値図式との可換式で引き戻す。
規約：底のパラメータを変更しない。
使われ方：底を固定した path の両端の相対持ち上げ性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：fiber ごとの関手を形状射で制限する。
方針：前合成の自然性と定値図式の制限を引き戻しへ送る。
規約：同じ底の頂点。使われ方：相対内部 Hom の制限の底変換。 -/
def fiberwiseFunctorRestriction {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p A :=
  pullback.map ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B)
    ((pre i).app E) (𝟙 B) ((pre i).app B)
    (by exact ((pre i).naturality p).symm)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.constantDiagram_pre, Category.id_comp])

/-- 概要：形状制限の関手成分は元の関手成分の前合成。
方針：引き戻しの第一射影。規約：厳密な等式。使われ方：相対制限の同定。 -/
lemma fiberwiseFunctorRestriction_fst {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K) :
    fiberwiseFunctorRestriction p i ≫ pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B) =
      pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) ≫ (pre i).app E :=
  pullback.lift_fst _ _ _

/-- 概要：形状制限は共有する底射を保つ。
方針：引き戻しの第二射影。規約：全パラメータで固定。使われ方：底上の持ち上げ。 -/
lemma fiberwiseFunctorRestriction_projection {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K) :
    fiberwiseFunctorRestriction p i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p K := by
  rw [fiberwiseFunctorRestriction, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection, pullback.map,
    pullback.lift_snd, Category.comp_id]
  rfl

/-- 概要：制限された図式と同じ底の全形状の定値図式を相対内部 Hom の底へ入れる。
方針：定値図式の制限式を使って引き戻しへ持ち上げる。
規約：元の底を保持。使われ方：相対内部 Hom の底変換の下辺。 -/
def fiberwiseRestrictionBase {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K)
    (r : internalHom.PullbackObjObj i p) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p A ⟶ r.pt :=
  r.isPullback.lift (pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) (by
      change pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B) ≫ (ihom A).map p =
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B) ≫ (pre i).app B
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.constantDiagram_pre]
      exact pullback.condition)

/-- 概要：相対制限の下辺の第一成分は元の制限された関手。
方針：引き戻しの第一射影。規約：厳密な等式。使われ方：底変換の可換式。 -/
lemma fiberwiseRestrictionBase_fst {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K)
    (r : internalHom.PullbackObjObj i p) :
    fiberwiseRestrictionBase p i r ≫ r.fst =
      pullback.fst ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram A B) := r.isPullback.lift_fst _ _ _

/-- 概要：相対制限の下辺の第二成分は元の底の定値全図式。
方針：引き戻しの第二射影。規約：元の底射。使われ方：底変換の可換式。 -/
lemma fiberwiseRestrictionBase_snd {A K E B : SSet.{u}} (p : E ⟶ B) (i : A ⟶ K)
    (r : internalHom.PullbackObjObj i p) :
    fiberwiseRestrictionBase p i r ≫ r.snd =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B := r.isPullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
