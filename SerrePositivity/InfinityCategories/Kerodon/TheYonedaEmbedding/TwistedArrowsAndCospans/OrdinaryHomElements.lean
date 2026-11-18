module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：通常圏の Hom 二変数関手とその元の圏を、指定した両端射影とともに読む。
方針：既存の coyoneda の uncurry と Mathlib の Elements をそのまま使う。
規約：射の関係は u ≫ f ≫ v = g で、第一成分だけが反変。
使われ方：Kerodon Remark 8.1.0.3（Tag 03JC）・Proposition 8.1.1.10（Tag 03JN）、
HTT 5.1.5.6 の S8 の元の Yoneda との比較の証明分割。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 通常の Hom の共同評価は既存の coyoneda を uncurry した関手。
Kerodon Remark 8.1.0.3（Tag 03JC）、両変数を同時に保持する入力。 -/
def ordinaryHomBifunctor (C : Type u) [SmallCategory C] : Cᵒᵖ × C ⥤ Type u :=
  Functor.uncurry.obj coyoneda

/-- 通常の twisted arrow の対象を Hom 関手の元の圏として読む既存模型。
Kerodon Remark 8.1.0.3（Tag 03JC）。新しい圏構造を選ばない。 -/
abbrev OrdinaryHomElements (C : Type u) [SmallCategory C] :=
  (ordinaryHomBifunctor C).Elements

/-- Hom 関手の元の圏の指定両端射影。
Kerodon Remark 8.1.0.3（Tag 03JC）、元の Elements の射影そのもの。 -/
abbrev ordinaryHomElementsProjection (C : Type u) [SmallCategory C] :
    OrdinaryHomElements C ⥤ Cᵒᵖ × C := Functor.Elements.π (ordinaryHomBifunctor C)

/-- 元の圏の射の条件を、第一成分が逆向きの同じ可換四角形で読む。
Kerodon Remark 8.1.0.3（Tag 03JC）、構成の値の計算則。 -/
lemma ordinaryHomElements_map_val {C : Type u} [SmallCategory C]
    {x y : OrdinaryHomElements C} (h : x ⟶ y) :
    h.hom.1.unop ≫ x.val ≫ h.hom.2 = y.val := by
  have hh := h.map_val
  change (h.hom.1.unop ≫ x.val) ≫ h.hom.2 = y.val at hh
  simpa only [Category.assoc] using hh

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
