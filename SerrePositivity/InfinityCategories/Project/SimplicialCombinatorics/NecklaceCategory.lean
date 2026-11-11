module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceSimplicialSet

/-! # 全端点保存写像を持つ元の necklace 圏
概要：元の necklace の実単体集合間の、両端点を保つ全写像を射とする。
方針：高次単体の写像をそのまま保持し、恒等・合成を実単体的写像から継承する。
規約：射を生成語に限定しない。使われ方：原典の necklace に沿う cubical 余極限。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 宇宙を固定した、有限 necklace の全ての形。 -/
abbrev Necklace := ULift.{u} _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape

/-- 元の両端点を保つ実単体的写像。 -/
@[ext] structure NecklaceHom (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) where
  map : T.down.carrier.{u} ⟶ U.down.carrier.{u}
  map_first : map.app _ T.down.firstVertex = U.down.firstVertex
  map_last : map.app _ T.down.lastVertex = U.down.lastVertex

/-- 元のすべての端点保存写像を持つ necklace 圏。 -/
instance necklaceCategory : Category.{u} _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} where
  Hom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom
  id T := ⟨𝟙 _, rfl, rfl⟩
  comp f g :=
    { map := f.map ≫ g.map
      map_first := by
        change g.map.app _ (f.map.app _ _) = _
        rw [f.map_first, g.map_first]
      map_last := by
        change g.map.app _ (f.map.app _ _) = _
        rw [f.map_last, g.map_last] }
  id_comp f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext (Category.id_comp f.map)
  comp_id f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext (Category.comp_id f.map)
  assoc f g h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext (Category.assoc f.map g.map h.map)

/-- 元の necklace の実単体集合と元の全射への忠実な関手。 -/
def necklaceSimplicialSet : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ SSet.{u} where
  obj T := T.down.carrier
  map f := f.map

/-- 元の necklace 射の等号は実単体的写像の等号で判定される。 -/
instance necklaceSimplicialSet_faithful : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet.{u}.Faithful where
  map_injective h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext h

/-- 恒等写像は元の単体集合の恒等写像。 -/
lemma necklace_id_map (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : (𝟙 T : T ⟶ T).map = 𝟙 T.down.carrier := rfl

/-- 合成写像は元の単体的写像の合成。 -/
lemma necklace_comp_map {T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    (f ≫ g).map = f.map ≫ g.map := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.Necklace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplicialSet := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet_faithful (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplicialSet_faithful := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet_faithful

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklace_comp_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_comp_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklace_id_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_id_map

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.ext := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.ext_iff := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.map_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.map_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.map_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.map_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.recOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_11 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_12 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_13 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_14 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_14

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_15 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_15

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceCategory._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceCategory._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplicialSet._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplicialSet._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceHom.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.mk.sizeOf_spec
