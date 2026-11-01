module
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceSimplicialSet

/-! # 全端点保存写像を持つ元の necklace 圏
概要：元の necklace の実単体集合間の、両端点を保つ全写像を射とする。
方針：高次単体の写像をそのまま保持し、恒等・合成を実単体的写像から継承する。
規約：射を生成語に限定しない。使われ方：原典の necklace に沿う cubical 余極限。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 宇宙を固定した、有限 necklace の全ての形。 -/
abbrev Necklace := ULift.{u} NecklaceShape

/-- 元の両端点を保つ実単体的写像。 -/
@[ext] structure NecklaceHom (T U : Necklace.{u}) where
  map : T.down.carrier.{u} ⟶ U.down.carrier.{u}
  map_first : map.app _ T.down.firstVertex = U.down.firstVertex
  map_last : map.app _ T.down.lastVertex = U.down.lastVertex

/-- 元のすべての端点保存写像を持つ necklace 圏。 -/
instance necklaceCategory : Category.{u} Necklace.{u} where
  Hom := NecklaceHom
  id T := ⟨𝟙 _, rfl, rfl⟩
  comp f g :=
    { map := f.map ≫ g.map
      map_first := by
        change g.map.app _ (f.map.app _ _) = _
        rw [f.map_first, g.map_first]
      map_last := by
        change g.map.app _ (f.map.app _ _) = _
        rw [f.map_last, g.map_last] }
  id_comp f := NecklaceHom.ext (Category.id_comp f.map)
  comp_id f := NecklaceHom.ext (Category.comp_id f.map)
  assoc f g h := NecklaceHom.ext (Category.assoc f.map g.map h.map)

/-- 元の necklace の実単体集合と元の全射への忠実な関手。 -/
def necklaceSimplicialSet : Necklace.{u} ⥤ SSet.{u} where
  obj T := T.down.carrier
  map f := f.map

/-- 元の necklace 射の等号は実単体的写像の等号で判定される。 -/
instance necklaceSimplicialSet_faithful : necklaceSimplicialSet.{u}.Faithful where
  map_injective h := NecklaceHom.ext h

/-- 恒等写像は元の単体集合の恒等写像。 -/
lemma necklace_id_map (T : Necklace.{u}) : (𝟙 T : T ⟶ T).map = 𝟙 T.down.carrier := rfl

/-- 合成写像は元の単体的写像の合成。 -/
lemma necklace_comp_map {T U V : Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    (f ≫ g).map = f.map ≫ g.map := rfl

end SerrePositivity.KST.SConstruction
