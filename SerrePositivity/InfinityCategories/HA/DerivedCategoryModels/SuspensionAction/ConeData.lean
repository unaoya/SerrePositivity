module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.Perfect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSuspensionCanonicalMapData

/-!
概要：代表化した実延長を K-B3 の同じ cone・平坦分解の射データへ接続する。
方針：元の ofConeFunctor と、射影的源の perfect 保存を使用する。
規約：任意の cone 間の実像比較が仮定。全単体作用の存在は結論しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R C D) {κ : Cardinal.{u}}
  (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D (dgModuleExtension R C D F) I.objects J.objects)

/-- 固定 cone の間の実延長に対する K-B3 正本の strict data。 -/
def dgModuleStrictImageSuspensionMapData : DGKappaSuspensionMapData R C D I J :=
  DGKappaSuspensionMapData.ofConeFunctor R C D I J
    (e.functor R C D _ I.objects J.objects)
    (fun M hM => e.preservesPerfect R C D F I.objects J.objects I.projective M hM)

/-- 元の cone 関手は代表化した同じ全 Hom 共役関手である。 -/
lemma dgModuleStrictImageSuspensionMapData_cone :
    (dgModuleStrictImageSuspensionMapData R C D F I J e).cone =
      e.functor R C D _ I.objects J.objects := rfl

/-- 固定平坦分解への増大は既存の正本比較によって厳密に可換する。 -/
lemma dgModuleStrictImageSuspensionMapData_augmentation :
    (dgModuleStrictImageSuspensionMapData R C D F I J e).resolved.comp
      (DGCategoryCellResolution.augmentation R (DGKappaCone R D J)) =
    (DGCategoryCellResolution.augmentation R (DGKappaCone R C I)).comp
      (e.functor R C D _ I.objects J.objects) :=
  (dgModuleStrictImageSuspensionMapData R C D F I J e).augmentation

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
