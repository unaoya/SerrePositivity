module
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceJointImage
public import Mathlib.Order.Category.PartOrd

/-! # joints を含む元の全頂点部分集合の関手
概要：原典の P(T) を、元の全 joints を含む有限頂点部分集合の順序集合として作る。
方針：全 necklace 射の作用は実頂点写像による像で定義し、joints 被覆で閉性を示す。
規約：定数一・定数零の座標を省略しない。使われ方：具体的立方体への作用の回収。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
namespace NecklaceShape

/-- 元の全 joints を含む頂点部分集合。 -/
abbrev CubeSubset (T : NecklaceShape) := {s : Finset T.Vertex // T.jointVertices ⊆ s}

/-- 元の最小頂点部分集合は、すべての joints そのもの。 -/
def cubeSubsetBottom (T : NecklaceShape) : T.CubeSubset := ⟨T.jointVertices, fun _ h => h⟩

/-- 元の最大頂点部分集合は、すべての頂点。 -/
def cubeSubsetTop (T : NecklaceShape) : T.CubeSubset := ⟨Finset.univ, Finset.subset_univ _⟩

/-- 元の二つの部分集合の join は同じ有限和集合。 -/
def cubeSubsetJoin (T : NecklaceShape) (s t : T.CubeSubset) : T.CubeSubset :=
  ⟨s.val ∪ t.val, fun _j hj => Finset.mem_union_left _ (s.property hj)⟩

end NecklaceShape

/-- 元の全 necklace 射は、joints を含む部分集合を同じ頂点写像の像に送る。 -/
def necklaceSubsetMap {T U : Necklace.{u}} (f : T ⟶ U) :
    T.down.CubeSubset →o U.down.CubeSubset where
  toFun s :=
    ⟨s.val.image (necklaceVertexMap f), by
      intro v hv
      obtain ⟨j, hj, hfj⟩ := necklaceVertexMap_joint_covered f v
        ((U.down.mem_jointVertices v).1 hv)
      exact Finset.mem_image.mpr ⟨j, s.property ((T.down.mem_jointVertices j).2 hj), hfj⟩⟩
  monotone' _ _ h := Finset.image_subset_image h

/-- 元の部分集合の恒等作用は恒等写像。 -/
lemma necklaceSubsetMap_id (T : Necklace.{u}) : necklaceSubsetMap (𝟙 T) = OrderHom.id := by
  apply DFunLike.ext
  intro s
  apply Subtype.ext
  change s.val.image (necklaceVertexMap (𝟙 T)) = s.val
  rw [necklaceVertexMap_id, Finset.image_id]

/-- 元の部分集合の作用は、元の necklace 射の合成を厳密に保つ。 -/
lemma necklaceSubsetMap_comp {T U V : Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    necklaceSubsetMap (f ≫ g) = (necklaceSubsetMap g).comp (necklaceSubsetMap f) := by
  apply DFunLike.ext
  intro s
  apply Subtype.ext
  change s.val.image (necklaceVertexMap (f ≫ g)) =
    (s.val.image (necklaceVertexMap f)).image (necklaceVertexMap g)
  rw [necklaceVertexMap_comp, Finset.image_image]

/-- 元の necklace 射の作用は、同じ部分集合の有限 join を保つ。 -/
lemma necklaceSubsetMap_join {T U : Necklace.{u}} (f : T ⟶ U)
    (s t : T.down.CubeSubset) :
    necklaceSubsetMap f (T.down.cubeSubsetJoin s t) =
      U.down.cubeSubsetJoin (necklaceSubsetMap f s) (necklaceSubsetMap f t) := by
  apply Subtype.ext
  exact Finset.image_union _ _

/-- 原典の全 joints を含む頂点部分集合と元の像作用を持つ順序集合値関手。 -/
def necklaceSubsetPoset : Necklace.{u} ⥤ PartOrd where
  obj T := PartOrd.of T.down.CubeSubset
  map f := PartOrd.ofHom (necklaceSubsetMap f)
  map_id T := PartOrd.Hom.ext (necklaceSubsetMap_id T)
  map_comp f g := PartOrd.Hom.ext (necklaceSubsetMap_comp f g)

end SerrePositivity.KST.SConstruction
