module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-! # 二つの空間値図式を同時に含む、小さいパラメータ単体集合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Fibration

/-- 全単体を二つの元の図式からそのまま取る和。 -/
def diagramSumSource (X Y : SSet.{u}) : SSet.{u} where
  obj n := X.obj n ⊕ Y.obj n
  map f := ↾Sum.map (X.map f) (Y.map f)
  map_id n := by
    apply ConcreteCategory.hom_ext
    rintro (x | y)
    · change Sum.inl (X.map (𝟙 n) x) = Sum.inl x
      exact congrArg Sum.inl (Functor.map_id_apply X n x)
    · change Sum.inr (Y.map (𝟙 n) y) = Sum.inr y
      exact congrArg Sum.inr (Functor.map_id_apply Y n y)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro (x | y)
    · change Sum.inl (X.map (f ≫ g) x) = Sum.inl (X.map g (X.map f x))
      exact congrArg Sum.inl (Functor.map_comp_apply X f g x)
    · change Sum.inr (Y.map (f ≫ g) y) = Sum.inr (Y.map g (Y.map f y))
      exact congrArg Sum.inr (Functor.map_comp_apply Y f g y)

/-- 和の第一因子への元の包含。 -/
def diagramSumInl (X Y : SSet.{u}) : X ⟶ diagramSumSource X Y where
  app _ := ↾Sum.inl
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 和の第二因子への元の包含。 -/
def diagramSumInr (X Y : SSet.{u}) : Y ⟶ diagramSumSource X Y where
  app _ := ↾Sum.inr
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

end SerrePositivity.KST.Fibration
