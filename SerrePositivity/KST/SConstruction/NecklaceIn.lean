module
public import SerrePositivity.KST.SConstruction.NecklaceCategory

/-! # 固定した両端点を持つ単体集合内の necklaces
概要：単体集合 K 内の x から y への全 necklace と元の可換三角形の圏を作る。
方針：実単体的写像の可換三角形をそのまま射とし、恒等と合成を継承する。
規約：necklace 写像の高次単体を保持。使われ方：rigidification の mapping object の添字。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- K 内の x から y への元の全単体的 necklace。 -/
structure NecklaceIn (K : SSet.{u}) (x y : K _⦋0⦌) where
  necklace : Necklace.{u}
  map : necklace.down.carrier ⟶ K
  map_first : map.app _ necklace.down.firstVertex = x
  map_last : map.app _ necklace.down.lastVertex = y

/-- 元の necklace 射による、K 内での実可換三角形。 -/
@[ext] structure NecklaceInHom {K : SSet.{u}} {x y : K _⦋0⦌} (T U : NecklaceIn K x y) where
  necklaceHom : T.necklace ⟶ U.necklace
  w : necklaceHom.map ≫ U.map = T.map

/-- 固定した両端点を持つ K 内の全 necklace の圏。 -/
instance necklaceInCategory (K : SSet.{u}) (x y : K _⦋0⦌) : Category (NecklaceIn K x y) where
  Hom := NecklaceInHom
  id T := ⟨𝟙 _, Category.id_comp _⟩
  comp f g :=
    { necklaceHom := f.necklaceHom ≫ g.necklaceHom
      w := by
        rw [necklace_comp_map, Category.assoc, g.w, f.w] }
  id_comp f := NecklaceInHom.ext (Category.id_comp f.necklaceHom)
  comp_id f := NecklaceInHom.ext (Category.comp_id f.necklaceHom)
  assoc f g h := NecklaceInHom.ext (Category.assoc f.necklaceHom g.necklaceHom h.necklaceHom)

/-- K 内の necklace から元の necklace を取り出す忠実な関手。 -/
def necklaceInForget (K : SSet.{u}) (x y : K _⦋0⦌) : NecklaceIn K x y ⥤ Necklace.{u} where
  obj T := T.necklace
  map f := f.necklaceHom

/-- 可換三角形は元の necklace 射の等号で判定できる。 -/
instance necklaceInForget_faithful (K : SSet.{u}) (x y : K _⦋0⦌) :
    (necklaceInForget K x y).Faithful where
  map_injective h := NecklaceInHom.ext h

/-- 元の全 necklace の実単体集合への図式。 -/
def necklaceInDiagram (K : SSet.{u}) (x y : K _⦋0⦌) : NecklaceIn K x y ⥤ SSet.{u} :=
  necklaceInForget K x y ⋙ necklaceSimplicialSet

/-- 元の全 necklace の K への写像は、同じ可換三角形の自然な族をなす。 -/
def necklaceInAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) :
    necklaceInDiagram K x y ⟶ (Functor.const (NecklaceIn K x y)).obj K where
  app T := T.map
  naturality T U f := by
    change f.necklaceHom.map ≫ U.map = T.map ≫ 𝟙 K
    rw [f.w, Category.comp_id]

end SerrePositivity.KST.SConstruction
