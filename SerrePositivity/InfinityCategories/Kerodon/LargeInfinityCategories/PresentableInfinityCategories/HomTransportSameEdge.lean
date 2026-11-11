module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConstantEvaluationHomTransport

/-!
概要：同じ一次単体の二つの表示を共通の両端へ輸送して照合する。
方針：端点の等式を消去し、辺の外延性を使う。
規約：元の代表辺を変更しない。
使われ方：変数交換した単位と native な余錐単位の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SSet.Truncated.HomotopyCategory

/-- 概要：同じ代表一次単体を共通の端点へ輸送すると同じ Hom 類を得る。
方針：全端点の等式を消去する。
規約：標的の充填性は不要。
使われ方：全単位と普遍余錐の単位の一致。 -/
lemma homMk_transport_sameEdge {X : SSet.{u}} {a b c d x y : X _⦋0⦌}
    (ha : a = x) (hb : b = y) (hc : c = x) (hd : d = y)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) a b)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) c d)
    (hef : e.edge = f.edge) :
    eqToHom (congrArg HomotopyCategory.mk ha).symm ≫ homMk e ≫
      eqToHom (congrArg HomotopyCategory.mk hb) =
    eqToHom (congrArg HomotopyCategory.mk hc).symm ≫ homMk f ≫
      eqToHom (congrArg HomotopyCategory.mk hd) := by
  subst a b c d
  have h : e = f := SSet.Truncated.Edge.ext hef
  subst f
  simp

/-- 概要：頂点の等式による射の定値化は同じ定値頂点の等式による射。
方針：頂点の等式を消去し、恒等射の定値化を使う。
規約：任意のパラメータを扱う。
使われ方：普遍余錐の頂点表示の輸送。 -/
lemma constantFunctorHomMap_eqToHom (A : SSet.{u}) {X : SSet.{u}} {x y : X _⦋0⦌}
    (h : x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (eqToHom (congrArg HomotopyCategory.mk h)) =
      eqToHom (congrArg (fun z ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : A ⟶ X))) h) := by
  subst y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id A x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
