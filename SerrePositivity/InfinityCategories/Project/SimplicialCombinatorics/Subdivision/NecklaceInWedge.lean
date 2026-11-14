module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeFunctor
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceIn

/-! # 単体集合内の固定端点 necklace の連結
概要：x から y、y から z への全 necklace と可換三角形を連結する。
方針：共有頂点の像の一致から native な wedge の普遍性を適用する。
規約：全高次単体的写像を保持。使われ方：cubical mapping object の合成の添字。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 固定された中間頂点で、元の一点からの二つの射が全単体的に一致する。 -/
lemma necklaceInWedge_seam {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    T.necklace.down.pointMap T.necklace.down.last ≫ T.map =
      U.necklace.down.pointMap U.necklace.down.first ≫ U.map :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_comp_eq _ _ T.map U.map (T.map_last.trans U.map_first.symm)

/-- 元の K 内の二つの necklace を、共有する元の頂点で貼る。 -/
def necklaceInWedge {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x z where
  necklace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T.necklace U.necklace
  map := T.necklace.down.wedgeDesc U.necklace.down T.map U.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)
  map_first := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.necklace.down.wedgeInl_desc U.necklace.down T.map U.map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)) _) T.necklace.down.firstVertex
    change (T.necklace.down.wedgeDesc U.necklace.down T.map U.map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)).app _
        ((T.necklace.down.wedgeInl U.necklace.down).app _ T.necklace.down.firstVertex) =
          T.map.app _ T.necklace.down.firstVertex at e
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_first, T.map_first] at e
    exact e
  map_last := by
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app
      (T.necklace.down.wedgeInr_desc U.necklace.down T.map U.map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)) _) U.necklace.down.lastVertex
    change (T.necklace.down.wedgeDesc U.necklace.down T.map U.map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)).app _
        ((T.necklace.down.wedgeInr U.necklace.down).app _ U.necklace.down.lastVertex) =
          U.map.app _ U.necklace.down.lastVertex at e
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_last, U.map_last] at e
    exact e

/-- 元の左 necklace への制限は、その元の K への写像を回収する。 -/
lemma necklaceInWedge_inl {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    T.necklace.down.wedgeInl U.necklace.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).map = T.map :=
  T.necklace.down.wedgeInl_desc U.necklace.down T.map U.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)

/-- 元の右 necklace への制限は、その元の K への写像を回収する。 -/
lemma necklaceInWedge_inr {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    T.necklace.down.wedgeInr U.necklace.down ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).map = U.map :=
  T.necklace.down.wedgeInr_desc U.necklace.down T.map U.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)

/-- 両側の元の可換三角形を、同じ K 内の可換三角形へ連結する。 -/
def necklaceInWedgeMap {K : SSet.{u}} {x y z : K _⦋0⦌}
    {T T' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} {U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z} (f : T ⟶ T') (g : U ⟶ U') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T' U' where
  necklaceHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f.necklaceHom g.necklaceHom
  w := by
    change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f.necklaceHom g.necklaceHom).map ≫
      T'.necklace.down.wedgeDesc U'.necklace.down T'.map U'.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T' U') =
        T.necklace.down.wedgeDesc U.necklace.down T.map U.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U)
    apply T.necklace.down.wedge_hom_ext U.necklace.down
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_desc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_desc, f.w]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_desc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_desc, g.w]

/-- 固定端点の全 necklace の連結の、元の二変数関手。 -/
def necklaceInWedgeFunctor (K : SSet.{u}) (x y z : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y × _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z ⥤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x z where
  obj p := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge p.1 p.2
  map f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f.1 f.2
  map_id p := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_id p.1.necklace p.2.necklace)
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_comp f.1.necklaceHom g.1.necklaceHom f.2.necklaceHom g.2.necklaceHom)

/-- 連結後に元の necklace を取り出す作用は、元の wedge の二変数関手そのもの。 -/
lemma necklaceInWedgeFunctor_forget (K : SSet.{u}) (x y z : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor K x y z ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x z =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x y).prod (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K y z) ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeFunctor := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeFunctor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeFunctor_forget := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor_forget

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge_inl := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge_inr := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge_seam := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedgeMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap._proof_1
