module

public import SerrePositivity.InfinityCategories.F1.CoherentResolutionParameterizedMap

/-!
概要：旗の解像の右随伴を Kan 複体の単体的圏の豊穣関手にする。
方針：パラメーター付きの内部 Hom の評価を解像へ移し、各旗で単位と合成を計算する。
規約：Kan 複体の対象と Hom の宇宙は u。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、coherent な図式の自然な置換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：解像の右随伴が内部 Hom に誘導する単体的な作用。
方針：内部 Hom の評価をパラメーター付き写像として解像へ移し、curry する。
規約：始域と終域は任意の単体集合。
使われ方：Kerodon Proposition 4.6.7.16、右随伴の豊穣 Hom の作用。 -/
noncomputable def coherentResolutionEnrichedMap (X Y : SSet.{u}) :
    (ihom X).obj Y ⟶
      (ihom (coherentResolutionRightAdjoint.obj X)).obj (coherentResolutionRightAdjoint.obj Y) :=
  curry (coherentResolutionParameterizedMap (uncurry (𝟙 ((ihom X).obj Y))))

/-- 概要：解像の右随伴は Kan 複体の単体的圏の豊穣自己関手を定める。
方針：各旗における内部 Hom の評価で単位と合成を比較する。
規約：通常の関手の作用だけでなく全ての高次の Hom に作用する。
使われ方：Kerodon Corollary 5.6.0.6、任意の coherent な空間値図式に適用できる解像。 -/
noncomputable def coherentResolutionKanEnriched : EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u} where
  obj X := ⟨coherentResolutionRightAdjoint.obj X.obj, inferInstance⟩
  map X Y := coherentResolutionEnrichedMap X.obj Y.obj
  map_id X := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply ULift.ext
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    apply ULift.ext
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro s
    rfl

end SerrePositivity.InfinityCategories
