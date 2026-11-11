module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NecklaceNumericNormalForm
public import SerrePositivity.KST.SConstruction.CubicalPresheaf

/-! # 全 necklace 射を持つ元の具体的立方体関手
概要：元の実単体的 necklace 射を、同じ数値頂点写像を持つ具体的 cube 射へ送る。
方針：元の右端座標の順序つき max 表示から生成条件を証明して束ねる。
規約：全射を保持し、生成条件を追加仮定にしない。使われ方：rigidification の余極限図式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の necklace 射と同じ数値頂点作用を持つ実際の具体的 cube 射。 -/
def necklaceConcreteCubeMap {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.down.dimension :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericMap_generated f⟩

/-- 元の具体的 cube 射は、同じ necklace 射の全数値頂点作用を回収する。 -/
lemma necklaceConcreteCubeMap_val {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    (necklaceConcreteCubeMap f).val = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f := rfl

/-- 全 necklace 射を、元の面・削除・max connection からなる具体的 cube 圏へ送る関手。 -/
def necklaceConcreteCube : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  obj T := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension
  map f := necklaceConcreteCubeMap f
  map_id T := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap_id T)
  map_comp f g := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap_comp f g)

/-- 元の necklace を、同じ具体的 cube を表す cubical set へ送る関手。 -/
def necklaceCubicalSet : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ CubicalSet.{u} :=
  necklaceConcreteCube ⋙ cubicalYoneda

/-- 元の各 necklace の cubical set は同じ次元の元の表現可能立方体。 -/
lemma necklaceCubicalSet_obj (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    necklaceCubicalSet.obj T = cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) := rfl

/-- 元の necklace 射の cubical 作用は、同じ具体的 cube 射の Yoneda 作用。 -/
lemma necklaceCubicalSet_map {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    necklaceCubicalSet.map f = cubicalYoneda.map (necklaceConcreteCubeMap f) := rfl

end SerrePositivity.KST.SConstruction
