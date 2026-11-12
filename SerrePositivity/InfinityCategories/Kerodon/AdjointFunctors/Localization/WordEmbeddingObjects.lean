module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingCut
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowReflection

/-!
# 単射な語の遷移による元の zigzag の回収

概要：語の包含の像の各列から、元の同じ列を回収し、対象上の単射性を証明する。
方針：包含の切断と一列の区間合成を照合し、元の対象の外延性を使う。
規約：元の端点の等式と後ろ向きの弱同値を保持する。
使われ方：全語の graph 図式の proper 性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 対象の等式は、元の同じ位置の列の異種等式を与える。 -/
lemma Zigzag.arrow_heq_of_eq {C : Type u} [Category.{v} C] {W : MorphismProperty C}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (h : S = T) (i : Fin w.length) :
    HEq (S.arrow i) (T.arrow i) := by
  cases h
  rfl

namespace WordAction
variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
include hf

lemma vertex_image_castSucc (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (i : Fin a.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).vertex (f.orderHom i).castSucc = S.vertex i.castSucc :=
  congrArg S.vertex (f.cut_image_castSucc hf i)

lemma vertex_image_succ (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (i : Fin a.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).vertex (f.orderHom i).succ = S.vertex i.succ :=
  congrArg S.vertex (f.cut_image_succ hf i)

/-- 包含の像の列は、元の同じ列そのもの。 -/
lemma arrow_image_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (i : Fin a.length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).arrow (f.orderHom i)) (S.arrow i) := by
  have hseg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq (a.direction i) S
    (f.cut_image_castSucc hf i) (f.cut_image_succ hf i)
    (f.cut_monotone (Fin.castSucc_le_succ (f.orderHom i))) (Fin.castSucc_le_succ i)
    (fun j hj hj' => (f.fiber_direction (f.orderHom i) j hj hj').trans (f.direction_eq i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction _ i rfl)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S (a.direction i) (f.orderHom i) (f.direction_eq i)).trans
    (hseg.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent (a.direction i) S i rfl)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) S (a.direction i) (f.orderHom i) i
    (f.direction_eq i) rfl (congrArg S.vertex (f.cut_image_source hf i))
    (congrArg S.vertex (f.cut_image_target hf i)) h

/-- 単射な語の遷移は元の対象を同一視しない。 -/
lemma obj_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (W := W) (X := X) (Y := Y) f) := by
  intro S T h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro i
    obtain ⟨j, rfl⟩ := f.cut_surjective hf i
    have hv := congrArg (fun R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y => R.vertex j) h
    change S.vertex (f.cut j) = T.vertex (f.cut j) at hv
    exact hv
  · intro i
    exact (arrow_image_heq f hf S i).symm.trans
      ((Zigzag.arrow_heq_of_eq h (f.orderHom i)).trans (arrow_image_heq f hf T i))

/-- 単射な語の遷移は、元の全縦射を区別する。 -/
lemma functor_faithful : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) f).Faithful where
  map_injective := by
    intro S T η θ h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro i
    obtain ⟨j, rfl⟩ := f.cut_surjective hf i
    have hv := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T => k.app j) h
    change η.app (f.cut j) = θ.app (f.cut j) at hv
    exact hv

end WordAction
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
