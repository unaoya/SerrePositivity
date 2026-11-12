module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphTransition
public import SerrePositivity.EInfinity.Hammock.GraphEmbedding

/-!
# 元の E 代数の語の包含による graph の単射性

概要：任意の可換環上で、語の包含は同じ実際の zigzag と graph の包含を与える。
方針：構成済みの対象単射性・忠実性・全単体の単射性へ実際の弱同値を代入する。
規約：モデル構造を局所的に選び、対象の cofibrancy やモデルの追加入力は不要。
使われ方：同じ元の E 代数の hammock 図式の proper 性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra)
include hf

lemma algebraHammockTransition_obj_injective :
    Function.Injective (algebraHammockTransition A f X Y).obj := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_injective f hf

lemma algebraHammockTransition_faithful : (algebraHammockTransition A f X Y).Faithful := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor_faithful f hf

/-- 同じ元の語の包含は、実際の全語の graph の単射。 -/
lemma algebraHammockGraphMap_mono : Mono (algebraHammockGraphMap A f X Y) := by
  have := algebraHammockTransition_faithful A f hf X Y
  exact Hammock.nerveMap_mono_of_faithful _ (algebraHammockTransition_obj_injective A f hf X Y)

/-- 同じ包含は元の全次数の全単体を区別する。 -/
lemma algebraHammockGraphMap_app_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((algebraHammockGraphMap A f X Y).app n) := by
  have := algebraHammockGraphMap_mono A f hf X Y
  exact CategoryTheory.injective_of_mono _

/-- 元の各列は、同じ像の位置の列からそのまま回収する。 -/
lemma algebraHammockTransition_image_arrow_heq (S : algebraHammockZigzag A a X Y)
    (i : Fin a.length) :
    HEq (((algebraHammockTransition A f X Y).obj S).arrow (f.orderHom i)) (S.arrow i) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq f hf S i

end SerrePositivity.EInfinity.BarrattEccles
