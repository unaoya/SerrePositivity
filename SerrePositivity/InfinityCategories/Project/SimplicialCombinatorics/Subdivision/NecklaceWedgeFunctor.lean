module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePointNaturality
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgePushout
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceCategory
public import Mathlib.CategoryTheory.Products.Basic

/-! # 全 necklace 射に対する wedge の二変数関手
概要：両端点を保つ任意の元の単体的写像を、共有頂点で連結する。
方針：実押し出しの降下と左右包含による射の判定を使う。
規約：生成語への制限を加えない。使われ方：rigidification の合成の添字関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 二つの元の necklace を、終始点で連結する。 -/
abbrev necklaceWedge (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} := ⟨T.down.wedge U.down⟩

/-- 任意の両端点保存射は、連結先の共有頂点で全単体的に一致する。 -/
lemma necklaceWedgeMap_seam {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.pointMap T.down.last ≫ (f.map ≫ T'.down.wedgeInl U'.down) =
      U.down.pointMap U.down.first ≫ (g.map ≫ T'.down.wedgeInr U'.down) := by
  rw [← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_naturality f.map _ _ f.map_last,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_naturality g.map _ _ g.map_first]
  exact T'.down.wedge_seam U'.down

/-- 元の全端点保存射を、同じ実押し出し上で連結する。 -/
def necklaceWedgeMap {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T' U' where
  map := T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
    (g.map ≫ T'.down.wedgeInr U'.down) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)
  map_first := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.down.wedgeInl_desc U.down (f.map ≫ T'.down.wedgeInl U'.down)
        (g.map ≫ T'.down.wedgeInr U'.down) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)) _) T.down.firstVertex
    change (T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
      (g.map ≫ T'.down.wedgeInr U'.down) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)).app _
      ((T.down.wedgeInl U.down).app _ T.down.firstVertex) =
        (T'.down.wedgeInl U'.down).app _ (f.map.app _ T.down.firstVertex) at e
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_first, f.map_first, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_first] at e
    exact e
  map_last := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.down.wedgeInr_desc U.down (f.map ≫ T'.down.wedgeInl U'.down)
        (g.map ≫ T'.down.wedgeInr U'.down) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)) _) U.down.lastVertex
    change (T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
      (g.map ≫ T'.down.wedgeInr U'.down) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)).app _
      ((T.down.wedgeInr U.down).app _ U.down.lastVertex) =
        (T'.down.wedgeInr U'.down).app _ (g.map.app _ U.down.lastVertex) at e
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_last, g.map_last, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_last] at e
    exact e

/-- 連結射の左包含への制限は、元の左射と包含の合成。 -/
lemma necklaceWedgeMap_inl {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.wedgeInl U.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g).map =
      f.map ≫ T'.down.wedgeInl U'.down :=
  T.down.wedgeInl_desc U.down _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)

/-- 連結射の右包含への制限は、元の右射と包含の合成。 -/
lemma necklaceWedgeMap_inr {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.wedgeInr U.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g).map =
      g.map ≫ T'.down.wedgeInr U'.down :=
  T.down.wedgeInr_desc U.down _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_seam f g)

/-- 両側の恒等射の連結は、元の連結 necklace の恒等射。 -/
lemma necklaceWedgeMap_id (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (𝟙 T) (𝟙 U) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
  apply T.down.wedge_hom_ext U.down
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_id_map, Category.id_comp, Category.comp_id]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_id_map, Category.id_comp, Category.comp_id]

/-- 任意の両側の合成は、同じ連結射の合成を厳密に回収する。 -/
lemma necklaceWedgeMap_comp {T T' T'' U U' U'' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}}
    (f : T ⟶ T') (f' : T' ⟶ T'') (g : U ⟶ U') (g' : U' ⟶ U'') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (f ≫ f') (g ≫ g') = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f' g' := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
  apply T.down.wedge_hom_ext U.down
  · change _ = T.down.wedgeInl U.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g).map ≫ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl f g,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl f' g', _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_comp_map, Category.assoc]
  · change _ = T.down.wedgeInr U.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g).map ≫ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr f g,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr f' g', _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_comp_map, Category.assoc]

/-- 全端点保存単体的写像を持つ、元の necklace の連結の二変数関手。 -/
def necklaceWedgeFunctor : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} × _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} where
  obj p := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge p.1 p.2
  map f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f.1 f.2
  map_id p := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_id p.1 p.2
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_comp f.1 g.1 f.2 g.2

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
