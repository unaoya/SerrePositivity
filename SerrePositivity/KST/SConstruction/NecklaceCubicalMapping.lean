module
public import SerrePositivity.KST.SConstruction.NecklaceConcreteCube
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceIn

/-! # 元の固定端点 necklace 図式の cubical 余極限
概要：K 内の x から y への全 necklace から、表現可能立方体の余極限を構成する。
方針：元のすべての可換三角形を具体的 cube 関手と Yoneda に送り、普遍性を回収する。
規約：wedge による合成は後続で証明する。使われ方：cubical rigidification の mapping object。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet

/-- 元の全 necklace と可換三角形を同じ表現可能立方体へ送る図式。 -/
def necklaceCubicalDiagram (K : SSet.{u}) (x y : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y ⥤ CubicalSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x y ⋙ necklaceCubicalSet

/-- 元の固定端点 necklace の全表現可能立方体による cubical 余極限。 -/
def necklaceCubicalMapping (K : SSet.{u}) (x y : K _⦋0⦌) : CubicalSet.{u} :=
  colimit (necklaceCubicalDiagram K x y)

/-- 元の各 necklace が cubical 余極限へ定める生成射。 -/
def necklaceCubicalCell {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension) ⟶
      necklaceCubicalMapping K x y :=
  colimit.ι (necklaceCubicalDiagram K x y) T

/-- 元のすべての可換三角形による生成射の関係式。 -/
lemma necklaceCubicalCell_relation {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U) :
    cubicalYoneda.map (necklaceConcreteCubeMap f.necklaceHom) ≫ necklaceCubicalCell U =
      necklaceCubicalCell T :=
  colimit.w (necklaceCubicalDiagram K x y) f

/-- 元の全 necklace の生成射で、同じ cubical mapping object からの射を判定する。 -/
lemma necklaceCubicalMapping_hom_ext {K : SSet.{u}} {x y : K _⦋0⦌} {M : CubicalSet.{u}}
    {f g : necklaceCubicalMapping K x y ⟶ M}
    (h : ∀ T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y, necklaceCubicalCell T ≫ f = necklaceCubicalCell T ≫ g) :
    f = g :=
  colimit.hom_ext h

variable {K : SSet.{u}} {x y : K _⦋0⦌} (M : CubicalSet.{u})
  (s : ∀ T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y,
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension) ⟶ M)
  (hs : ∀ {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U),
    cubicalYoneda.map (necklaceConcreteCubeMap f.necklaceHom) ≫ s U = s T)

/-- 元の可換三角形の全表示関係を満たす族の cubical 余錐。 -/
def necklaceCubicalCocone : Cocone (necklaceCubicalDiagram K x y) where
  pt := M
  ι :=
    { app := s
      naturality := fun _ _ f => by
        change cubicalYoneda.map (necklaceConcreteCubeMap f.necklaceHom) ≫ _ = _ ≫ 𝟙 M
        rw [hs f, Category.comp_id] }

/-- 元の全 necklace で指定した射の族を、同じ mapping object へ降ろす。 -/
def necklaceCubicalDesc : necklaceCubicalMapping K x y ⟶ M :=
  colimit.desc (necklaceCubicalDiagram K x y) (necklaceCubicalCocone M s hs)

/-- 元の降下は、元の全 necklace 上の指定した射を厳密に回収する。 -/
lemma necklaceCubicalDesc_cell (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    necklaceCubicalCell T ≫ necklaceCubicalDesc M s hs = s T :=
  colimit.ι_desc (necklaceCubicalCocone M s hs) T

end SerrePositivity.KST.SConstruction
