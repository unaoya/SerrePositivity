module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceCategory

/-! # 固定した両端点を持つ単体集合内の necklaces
概要：単体集合 K 内の x から y への全 necklace と元の可換三角形の圏を作る。
方針：実単体的写像の可換三角形をそのまま射とし、恒等と合成を継承する。
規約：necklace 写像の高次単体を保持。使われ方：rigidification の mapping object の添字。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- K 内の x から y への元の全単体的 necklace。 -/
structure NecklaceIn (K : SSet.{u}) (x y : K _⦋0⦌) where
  necklace : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}
  map : necklace.down.carrier ⟶ K
  map_first : map.app _ necklace.down.firstVertex = x
  map_last : map.app _ necklace.down.lastVertex = y

/-- 元の necklace 射による、K 内での実可換三角形。 -/
@[ext] structure NecklaceInHom {K : SSet.{u}} {x y : K _⦋0⦌} (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) where
  necklaceHom : T.necklace ⟶ U.necklace
  w : necklaceHom.map ≫ U.map = T.map

/-- 固定した両端点を持つ K 内の全 necklace の圏。 -/
instance necklaceInCategory (K : SSet.{u}) (x y : K _⦋0⦌) : Category (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) where
  Hom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom
  id T := ⟨𝟙 _, Category.id_comp _⟩
  comp f g :=
    { necklaceHom := f.necklaceHom ≫ g.necklaceHom
      w := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_comp_map, Category.assoc, g.w, f.w] }
  id_comp f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (Category.id_comp f.necklaceHom)
  comp_id f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (Category.comp_id f.necklaceHom)
  assoc f g h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (Category.assoc f.necklaceHom g.necklaceHom h.necklaceHom)

/-- K 内の necklace から元の necklace を取り出す忠実な関手。 -/
def necklaceInForget (K : SSet.{u}) (x y : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y ⥤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} where
  obj T := T.necklace
  map f := f.necklaceHom

/-- 可換三角形は元の necklace 射の等号で判定できる。 -/
instance necklaceInForget_faithful (K : SSet.{u}) (x y : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x y).Faithful where
  map_injective h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext h

/-- 元の全 necklace の実単体集合への図式。 -/
def necklaceInDiagram (K : SSet.{u}) (x y : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x y ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet

/-- 元の全 necklace の K への写像は、同じ可換三角形の自然な族をなす。 -/
def necklaceInAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInDiagram K x y ⟶ (Functor.const (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y)).obj K where
  app T := T.map
  naturality T U f := by
    change f.necklaceHom.map ≫ U.map = T.map ≫ 𝟙 K
    rw [f.w, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAugmentation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAugmentation := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAugmentation

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInDiagram := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInForget := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget_faithful (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInForget_faithful := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget_faithful

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.map_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.map_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.map_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.map_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.necklace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.necklace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.necklace

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.recOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.ext := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.ext_iff := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.necklaceHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.necklaceHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.necklaceHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.recOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.w := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.w

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAugmentation._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAugmentation._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInCategory._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInCategory._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInForget._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInForget._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceIn.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceInHom.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.mk.sizeOf_spec
