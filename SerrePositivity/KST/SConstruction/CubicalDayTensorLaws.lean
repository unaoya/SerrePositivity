module
public import SerrePositivity.KST.SConstruction.CubicalDayCells

/-! # 元の cubical Day tensor の関手性と cell 自然性
概要：全前層の元の射に関して、Day tensor の恒等・合成保存と連結 cell の自然性を回収する。
方針：同じ Day モノイダル構造の射の法則と、左 Kan 延長の単位との可換性を使う。
規約：元の前層と全ての cell を保持する。使われ方：necklace の関手性と鎖への延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open LawfulDayConvolutionMonoidalCategoryStruct

/-- 元の両恒等射の Day tensor は同じ Day tensor の恒等射。 -/
lemma cubicalDayTensorMap_id (K L : CubicalSet.{u}) :
    cubicalDayTensorMap (𝟙 K) (𝟙 L) = 𝟙 (cubicalDayTensor K L) :=
  congrArg DayFunctor.Hom.natTrans
    (MonoidalCategory.id_tensorHom_id (DayFunctor.mk K) (DayFunctor.mk L))

/-- 元の両射の合成の Day tensor は、同じ Day tensor 射の合成。 -/
lemma cubicalDayTensorMap_comp {K K' K'' L L' L'' : CubicalSet.{u}}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    cubicalDayTensorMap (f ≫ f') (g ≫ g') =
      cubicalDayTensorMap f g ≫ cubicalDayTensorMap f' g' := by
  have ht := MonoidalCategory.tensorHom_comp_tensorHom (C := CubicalDaySet.{u})
    (show DayFunctor.mk K ⟶ DayFunctor.mk K' from .mk f)
    (show DayFunctor.mk L ⟶ DayFunctor.mk L' from .mk g)
    (show DayFunctor.mk K' ⟶ DayFunctor.mk K'' from .mk f')
    (show DayFunctor.mk L' ⟶ DayFunctor.mk L'' from .mk g')
  exact congrArg DayFunctor.Hom.natTrans ht.symm

/-- 元の二つの前層の射の Day tensor は、元の連結 cell の作用を回収する。 -/
lemma cubicalDayTensorMap_cell {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalDayTensorMap f g).app (op (concreteCubeTensorObj c d))
        (cubicalDayTensorCell c d x y) =
      cubicalDayTensorCell c d (f.app (op c) x) (g.app (op d) y) := by
  have h := convolutionExtensionUnit_comp_ι_map_tensorHom_app _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)
      (show DayFunctor.mk K ⟶ DayFunctor.mk K' from DayFunctor.Hom.mk f)
      (show DayFunctor.mk L ⟶ DayFunctor.mk L' from DayFunctor.Hom.mk g) (op c) (op d)
  exact congrArg (fun t => t (x, y)) h

end SerrePositivity.KST.SConstruction
