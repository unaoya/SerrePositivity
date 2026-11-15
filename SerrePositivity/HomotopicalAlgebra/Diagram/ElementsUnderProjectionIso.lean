module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsUnderProjection
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：固定始点の要素圏の比較は、指定射影を持つ厳密な圏同型になる。
方針：持ち上げの終点の要素の等式を使い、既存の単位をeqToHomと照合する。
使われ方：HTT 4.2.4.4、RR02(a)のBK重みの同型による移送。
規約：単なる圏同値からnerveの同型を推論せず、厳密な逆を確認する。
-/

@[expose] public noncomputable section
universe w
open CategoryTheory
namespace SerrePositivity.DiagramModel.ElementsUnderProjection
variable {K : Type w} [SmallCategory K] (F : K ⥤ Type w) (e : F.Elements)

/-- 射影して持ち上げ直すと、元の固定始点の射そのものに戻る。 -/
lemma lift_post_obj (t : Under e) :
    (lift F e).obj ((Under.post (Functor.Elements.π F)).obj t) = t := by
  rcases t with ⟨l, r, h⟩
  rcases l with ⟨⟨⟩⟩
  rcases r with @⟨k, x⟩
  rcases h with ⟨f, h⟩
  change e.obj ⟶ k at f
  change F.map f e.val = x at h
  subst x
  rfl

/-- 逆向きの合成も元の射そのもの。 -/
lemma post_lift_obj (t : Under e.obj) :
    (Under.post (Functor.Elements.π F)).obj ((lift F e).obj t) = t := rfl

/-- 既存の単位は、上の対象の等式による射である。 -/
lemma unit_eq_eqToHom (t : Under e) :
    (unitComponent F e t).hom = eqToHom (lift_post_obj F e t).symm := by
  rcases t with ⟨l, r, h⟩
  rcases l with ⟨⟨⟩⟩
  rcases r with @⟨k, x⟩
  rcases h with ⟨f, h⟩
  change e.obj ⟶ k at f
  change F.map f e.val = x at h
  subst x
  rfl

/-- 指定射影を順方向に持つ厳密な圏同型。 -/
def catIso : Cat.of (Under e) ≅ Cat.of (Under e.obj) :=
  Cat.isoOfEquiv (equivalence F e) (lift_post_obj F e) (post_lift_obj F e)
    (unit_eq_eqToHom F e) (fun _ => rfl)

/-- 同じ指定射影のnerveは、実際の単体集合の同型になる。 -/
def nerveIso : nerve (Under e) ≅ nerve (Under e.obj) :=
  nerveFunctor.mapIso (catIso F e)

lemma nerveIso_hom : (nerveIso F e).hom =
    nerveMap (Under.post (Functor.Elements.π F) (X := e)) := rfl

end SerrePositivity.DiagramModel.ElementsUnderProjection
