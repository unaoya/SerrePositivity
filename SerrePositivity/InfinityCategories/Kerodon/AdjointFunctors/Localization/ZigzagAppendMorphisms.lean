module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical

/-!
# Zigzag の連結の元の可換縦射

概要：元の二つの可換縦射を、連結した zigzag の可換縦射として構成する。
方針：左右の全列を元の列と比較し、元の可換正方形を移す。
規約：接合点の条件は元の固定端点の条件から導き、追加入力にしない。
使われ方：固定語の graph の連結関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}
  {S S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {T T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z}

/-- 左側の全列の正方形は、元の同じ左の正方形。 -/
lemma left_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom T T') (i : Fin a.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).arrow (i.castAdd b.length) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.castAdd b.length)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.castAdd b.length)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S' T').arrow (i.castAdd b.length) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_left a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq f g (a.target i))
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_left a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq f g (a.source i))
  have hl := heq_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_left_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_left_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_left_eq S' T' i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S T i) ht
  have hr := heq_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_left_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_left_eq S' T' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_left_eq S' T' i)
    hs (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S' T' i)
  exact eq_of_heq (hl.trans ((heq_of_eq (f.comm i)).trans hr.symm))

/-- 右側の全列の正方形も、接合点を含めて元の同じ右の正方形。 -/
lemma right_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom T T') (i : Fin b.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).arrow (i.natAdd a.length) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.natAdd a.length)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.natAdd a.length)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S' T').arrow (i.natAdd a.length) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_right a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq f g (b.target i))
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_right a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq f g (b.source i))
  have hl := heq_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_right_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_right_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_right_eq S' T' i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq S T i) ht
  have hr := heq_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_right_eq S T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.source_right_eq S' T' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.target_right_eq S' T' i)
    hs (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq S' T' i)
  exact eq_of_heq (hl.trans ((heq_of_eq (g.comm i)).trans hr.symm))

/-- 元の全縦弱同値を連結した、実際の固定端点 zigzag の射。 -/
def map (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom T T') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S' T') where
  app := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app f g
  app_mem := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_mem f g
  first := by
    have h := (conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S' T' 0)).2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq f g 0)
    rw [f.first, eqToHom_trans, eqToHom_trans] at h
    exact h
  last := by
    have h := (conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T (Fin.last b.length))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S' T' (Fin.last b.length))).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq f g (Fin.last b.length))
    rw [g.last, eqToHom_trans, eqToHom_trans] at h
    exact h
  comm i := by
    cases i using Fin.addCases with
    | left i => exact left_comm f g i
    | right i => exact right_comm f g i

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms
