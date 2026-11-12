module
public import SerrePositivity.KST.SConstruction.CubicalDayTensor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Cubical 外積の各変数の余極限保存
概要：元の cubical 前層の外積が、左右それぞれの変数で余極限を保つ。
方針：各立方体対で評価し、Type の左右の直積関手の余極限保存に帰着する。
規約：Day tensor との比較前の元の外積を使う。使われ方：cubical 合成の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalCategory.ExternalProduct

/-- 元の左因子を固定した cubical 外積。 -/
def cubicalExternalLeft (K : CubicalSet.{u}) :
    CubicalSet.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ × _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⥤ Type u where
  obj L := K ⊠ L
  map f := (externalProductBifunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).map (𝟙 K, f)
  map_id L := by ext p z; rfl
  map_comp f g := by ext p z; rfl

/-- 元の右因子を固定した cubical 外積。 -/
def cubicalExternalRight (L : CubicalSet.{u}) :
    CubicalSet.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ × _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⥤ Type u where
  obj K := K ⊠ L
  map f := (externalProductBifunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).map (f, 𝟙 L)
  map_id K := by ext p z; rfl
  map_comp f g := by ext p z; rfl

/-- 左因子を固定した元の外積は、同じ前層圏の余極限を保つ。 -/
instance cubicalExternalLeft_preservesColimits (K : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalExternalLeft K) := by
  apply preservesColimits_of_evaluation
  intro p
  change PreservesColimitsOfSize.{u, u}
    ((evaluation _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).obj p.2 ⋙ tensorLeft (K.obj p.1))
  infer_instance

/-- 右因子を固定した元の外積は、同じ前層圏の余極限を保つ。 -/
instance cubicalExternalRight_preservesColimits (L : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalExternalRight L) := by
  apply preservesColimits_of_evaluation
  intro p
  change PreservesColimitsOfSize.{u, u}
    ((evaluation _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).obj p.1 ⋙ tensorRight (L.obj p.2))
  infer_instance

end SerrePositivity.KST.SConstruction
