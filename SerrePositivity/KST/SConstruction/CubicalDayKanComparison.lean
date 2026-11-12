module
public import SerrePositivity.KST.SConstruction.CubicalDayTensorLaws
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # 元の Day tensor と左 Kan 延長関手の比較
概要：元の全射に自然な比較同型で、Day tensor を左 Kan 延長関手に接続する。
方針：同じ外積に対する左 Kan 延長の一意性と、元の生成射の自然性を使う。
規約：比較は元の生成射を回収する。使われ方：Day tensor の余極限保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory.ExternalProduct

/-- 全ての元の射について、Day tensor の単位は外積との可換性を持つ。 -/
lemma cubicalDayTensorUnit_naturality {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    cubicalDayTensorUnit K L ≫ Functor.whiskerLeft _ (cubicalDayTensorMap f g) =
      (externalProductBifunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).map (f, g) ≫
        cubicalDayTensorUnit K' L' := by
  ext p z
  exact cubicalDayTensorMap_cell f g p.1.unop p.2.unop z.1 z.2

/-- 同じ外積の左 Kan 延長から元の Day tensor への比較同型。 -/
def cubicalDayKanIso (K L : CubicalSet.{u}) :
    (tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lan.obj (K ⊠ L) ≅ cubicalDayTensor K L :=
  Functor.leftKanExtensionUnique _
    ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).leftKanExtensionUnit (K ⊠ L)) _ (cubicalDayTensorUnit K L)

/-- 比較同型は元の左 Kan 延長の単位を厳密に回収する。 -/
lemma cubicalDayKanIso_unit (K L : CubicalSet.{u}) :
    (tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).leftKanExtensionUnit (K ⊠ L) ≫
        Functor.whiskerLeft _ (cubicalDayKanIso K L).hom = cubicalDayTensorUnit K L := by
  simp [cubicalDayKanIso, Functor.leftKanExtensionUnique,
    Functor.leftKanExtensionUniqueOfIso]

/-- 全ての元の射について、同じ Day tensor への比較は自然。 -/
lemma cubicalDayKanIso_naturality {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    (tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lan.map
        ((externalProductBifunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).map (f, g)) ≫
        (cubicalDayKanIso K' L').hom =
      (cubicalDayKanIso K L).hom ≫ cubicalDayTensorMap f g := by
  apply Functor.hom_ext_of_isLeftKanExtension _
    ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).leftKanExtensionUnit (K ⊠ L))
  ext p z
  let a : K ⊠ L ⟶ K' ⊠ L' :=
    (externalProductBifunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)).map
      (show (K, L) ⟶ (K', L') from (f, g))
  have hn := congr_app ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lanUnit.naturality a) p
  have ht := congr_app (cubicalDayKanIso_unit K' L') p
  have hs := congr_app (cubicalDayKanIso_unit K L) p
  have hd := congr_app (cubicalDayTensorUnit_naturality f g) p
  exact (congrArg ((cubicalDayKanIso K' L').hom.app
      ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).obj p)) (congrArg (fun t => t z) hn).symm).trans
    ((congrArg (fun t => t
      (a.app p z)) ht).trans
      ((congrArg (fun t => t z) hd).symm.trans
        (congrArg ((cubicalDayTensorMap f g).app ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).obj p))
          (congrArg (fun t => t z) hs).symm)))

end SerrePositivity.KST.SConstruction
