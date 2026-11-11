module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanPointHomEnriched

/-!
概要：任意の小さい単体集合を始点とする内部 Hom の全豊穣関手。
方針：値は標的の Kan 性で Kan 複体とし、全 Hom パラメーターの合成で高次射への作用を定める。
規約：始点の Kan 性を要求しない。通常の射だけに制限しない。
使われ方：有限単体集合の Kan 置換の compact 性と空間の小さい生成圏。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 任意の小さい単体集合始点からの内部 Hom を取る、全高次射の作用を持つ豊穣自己関手。 -/
def simplicialInternalHomEnriched (K : SSet.{u}) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj L := ⟨(ihom K).obj L.obj, inferInstance⟩
  map L M := curry (MonoidalClosed.comp K L.obj M.obj)
  map_id L := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, t⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    change f.app m (α ≫ 𝟙 m) x = f.app m α x
    rw [Category.comp_id]
  map_comp L M N := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g, h⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 同じ全豊穣 Hom 自己関手を、元の空間 ∞ 圏の全関手として実現する。 -/
def simplicialInternalHomInfinity (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (simplicialInternalHomEnriched K)

/-- 同じ Kan 内部 Hom の通常の全図式への作用。 -/
def simplicialInternalHomFunctor (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj L := (simplicialInternalHomEnriched K).obj L
  map f := (ihom K).map f
  map_id L := (ihom K).map_id L.obj
  map_comp f g := (ihom K).map_comp f g


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
