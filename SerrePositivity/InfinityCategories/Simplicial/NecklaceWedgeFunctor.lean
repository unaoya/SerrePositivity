module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklacePointNaturality
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgePushout
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceCategory
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
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 二つの元の necklace を、終始点で連結する。 -/
abbrev necklaceWedge (T U : Necklace.{u}) : Necklace.{u} := ⟨T.down.wedge U.down⟩

/-- 任意の両端点保存射は、連結先の共有頂点で全単体的に一致する。 -/
lemma necklaceWedgeMap_seam {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.pointMap T.down.last ≫ (f.map ≫ T'.down.wedgeInl U'.down) =
      U.down.pointMap U.down.first ≫ (g.map ≫ T'.down.wedgeInr U'.down) := by
  rw [← Category.assoc,
    NecklaceShape.pointMap_naturality f.map _ _ f.map_last,
    ← Category.assoc, NecklaceShape.pointMap_naturality g.map _ _ g.map_first]
  exact T'.down.wedge_seam U'.down

/-- 元の全端点保存射を、同じ実押し出し上で連結する。 -/
def necklaceWedgeMap {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    necklaceWedge T U ⟶ necklaceWedge T' U' where
  map := T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
    (g.map ≫ T'.down.wedgeInr U'.down) (necklaceWedgeMap_seam f g)
  map_first := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.down.wedgeInl_desc U.down (f.map ≫ T'.down.wedgeInl U'.down)
        (g.map ≫ T'.down.wedgeInr U'.down) (necklaceWedgeMap_seam f g)) _) T.down.firstVertex
    change (T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
      (g.map ≫ T'.down.wedgeInr U'.down) (necklaceWedgeMap_seam f g)).app _
      ((T.down.wedgeInl U.down).app _ T.down.firstVertex) =
        (T'.down.wedgeInl U'.down).app _ (f.map.app _ T.down.firstVertex) at e
    rw [NecklaceShape.wedgeInl_first, f.map_first, NecklaceShape.wedgeInl_first] at e
    exact e
  map_last := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.down.wedgeInr_desc U.down (f.map ≫ T'.down.wedgeInl U'.down)
        (g.map ≫ T'.down.wedgeInr U'.down) (necklaceWedgeMap_seam f g)) _) U.down.lastVertex
    change (T.down.wedgeDesc U.down (f.map ≫ T'.down.wedgeInl U'.down)
      (g.map ≫ T'.down.wedgeInr U'.down) (necklaceWedgeMap_seam f g)).app _
      ((T.down.wedgeInr U.down).app _ U.down.lastVertex) =
        (T'.down.wedgeInr U'.down).app _ (g.map.app _ U.down.lastVertex) at e
    rw [NecklaceShape.wedgeInr_last, g.map_last, NecklaceShape.wedgeInr_last] at e
    exact e

/-- 連結射の左包含への制限は、元の左射と包含の合成。 -/
lemma necklaceWedgeMap_inl {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.wedgeInl U.down ≫ (necklaceWedgeMap f g).map =
      f.map ≫ T'.down.wedgeInl U'.down :=
  T.down.wedgeInl_desc U.down _ _ (necklaceWedgeMap_seam f g)

/-- 連結射の右包含への制限は、元の右射と包含の合成。 -/
lemma necklaceWedgeMap_inr {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U') :
    T.down.wedgeInr U.down ≫ (necklaceWedgeMap f g).map =
      g.map ≫ T'.down.wedgeInr U'.down :=
  T.down.wedgeInr_desc U.down _ _ (necklaceWedgeMap_seam f g)

/-- 両側の恒等射の連結は、元の連結 necklace の恒等射。 -/
lemma necklaceWedgeMap_id (T U : Necklace.{u}) :
    necklaceWedgeMap (𝟙 T) (𝟙 U) = 𝟙 (necklaceWedge T U) := by
  apply NecklaceHom.ext
  apply T.down.wedge_hom_ext U.down
  · rw [necklaceWedgeMap_inl]
    simp only [necklace_id_map, Category.id_comp, Category.comp_id]
  · rw [necklaceWedgeMap_inr]
    simp only [necklace_id_map, Category.id_comp, Category.comp_id]

/-- 任意の両側の合成は、同じ連結射の合成を厳密に回収する。 -/
lemma necklaceWedgeMap_comp {T T' T'' U U' U'' : Necklace.{u}}
    (f : T ⟶ T') (f' : T' ⟶ T'') (g : U ⟶ U') (g' : U' ⟶ U'') :
    necklaceWedgeMap (f ≫ f') (g ≫ g') = necklaceWedgeMap f g ≫ necklaceWedgeMap f' g' := by
  apply NecklaceHom.ext
  apply T.down.wedge_hom_ext U.down
  · change _ = T.down.wedgeInl U.down ≫ (necklaceWedgeMap f g).map ≫ _
    rw [necklaceWedgeMap_inl, ← Category.assoc, necklaceWedgeMap_inl f g,
      Category.assoc, necklaceWedgeMap_inl f' g', necklace_comp_map, Category.assoc]
  · change _ = T.down.wedgeInr U.down ≫ (necklaceWedgeMap f g).map ≫ _
    rw [necklaceWedgeMap_inr, ← Category.assoc, necklaceWedgeMap_inr f g,
      Category.assoc, necklaceWedgeMap_inr f' g', necklace_comp_map, Category.assoc]

/-- 全端点保存単体的写像を持つ、元の necklace の連結の二変数関手。 -/
def necklaceWedgeFunctor : Necklace.{u} × Necklace.{u} ⥤ Necklace.{u} where
  obj p := necklaceWedge p.1 p.2
  map f := necklaceWedgeMap f.1 f.2
  map_id p := necklaceWedgeMap_id p.1 p.2
  map_comp f g := necklaceWedgeMap_comp f.1 g.1 f.2 g.2

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedge := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedge

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeFunctor := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_comp := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_id := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_inl := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_inl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_inr := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_seam := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_seam

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap._proof_2
