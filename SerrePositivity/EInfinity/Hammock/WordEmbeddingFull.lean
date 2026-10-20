module

public import SerrePositivity.EInfinity.Hammock.WordEmbeddingMapComponents

/-!
# 語の包含の元の遷移関手の充満性

概要：包含の像の間の全縦射を元の縦射として回収し、両逆を証明する。
方針：各成分の回収を元の列の正方形と端点条件に適用する。
規約：構成済みの語の作用を使い、別の関手で代用しない。
使われ方：包含の像の全単体の特徴付けと proper 性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y : C} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
  {S T : Zigzag W a X Y}
include hf

lemma embeddingApp_comm (g : obj f S ⟶ obj f T) (i : Fin a.length) :
    S.arrow i ≫ embeddingApp f hf g (a.target i) =
      embeddingApp f hf g (a.source i) ≫ T.arrow i := by
  have hs := f.cut_image_source hf i
  have ht := f.cut_image_target hf i
  have hL := heq_comp (congrArg S.vertex hs).symm (congrArg S.vertex ht).symm
    (congrArg T.vertex ht).symm (arrow_image_heq f hf S i).symm
    (embeddingApp_heq f hf g _ _ ht)
  have hR := heq_comp (congrArg S.vertex hs).symm (congrArg T.vertex hs).symm
    (congrArg T.vertex ht).symm (embeddingApp_heq f hf g _ _ hs)
    (arrow_image_heq f hf T i).symm
  exact eq_of_heq (hL.trans ((heq_of_eq (g.comm (f.orderHom i))).trans hR.symm))

/-- 同じ包含の像の間の縦射を回収する、元の縦射。 -/
def embeddingPreimage (g : obj f S ⟶ obj f T) : S ⟶ T where
  app := embeddingApp f hf g
  app_mem := embeddingApp_mem f hf g
  first := embeddingApp_first f hf g
  last := embeddingApp_last f hf g
  comm := embeddingApp_comm f hf g

lemma map_embeddingPreimage (g : obj f S ⟶ obj f T) : map f (embeddingPreimage f hf g) = g := by
  apply Zigzag.hom_ext
  intro j
  exact eq_of_heq (embeddingApp_heq f hf g (f.cut j) j rfl)

lemma embeddingPreimage_map (g : S ⟶ T) : embeddingPreimage f hf (map f g) = g := by
  have := functor_faithful (W := W) (X := X) (Y := Y) f hf
  apply (functor (W := W) (X := X) (Y := Y) f).map_injective
  exact map_embeddingPreimage f hf (map f g)

/-- 語の包含による元の遷移関手は充満。 -/
lemma functor_full : (functor (W := W) (X := X) (Y := Y) f).Full where
  map_surjective g := ⟨embeddingPreimage f hf g, map_embeddingPreimage f hf g⟩

end SerrePositivity.EInfinity.Hammock.WordAction
