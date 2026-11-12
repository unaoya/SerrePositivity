module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronForMorphisms
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronModelTransport

/-! # 安定 ∞ 圏のホモトピー圏の三角構造

概要：安定 quasicategory のホモトピー圏は cofiber 列の像を distinguished とする三角圏である。
方針：既存の前三角構造に対し、二長方形の八面体模型を任意の入力へ同型輸送する。
規約：既存の前加法構造と整数シフトを用いる。使われ方：HA 1.1.2.14、長完全列と完全関手。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 quasicategory のホモトピー圏は八面体公理を満たす。
方針：任意の二射の八面体模型を用い、任意の三つの distinguished 三角形へ輸送する。
規約：distinguished 集合は cofiber 列の像。追加の有限極限や余極限の仮定は不要。
使われ方：構成済み Pretriangulated instance とともに h C の三角構造を公開する。 -/
instance isTriangulated_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    IsTriangulated (hoFunctor.obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_of_octahedronModels (fun f g => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.octahedronModel_of_morphisms f g)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
