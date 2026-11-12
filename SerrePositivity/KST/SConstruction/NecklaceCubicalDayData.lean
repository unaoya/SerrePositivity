module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposition
public import SerrePositivity.KST.SConstruction.NecklaceCubicalIdentity
public import SerrePositivity.KST.SConstruction.CubicalDayWrappedColimits

/-! # 元の cubical mapping object の Day 圏での表示
概要：元の全 mapping object・生成射・単位・合成を同じ Day 圏で読む。
方針：元の前層の圏同値で包み、全生成射の回収と余極限の普遍性を保持する。
規約：元の射と厳密に一致する。使われ方：cubical rigidification の全構造法則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet

/-- 元の cubical mapping object を同じ Day 圏で読む。 -/
abbrev necklaceCubicalDayMapping (K : SSet.{u}) (x y : K _⦋0⦌) : CubicalDaySet.{u} :=
  DayFunctor.mk (necklaceCubicalMapping K x y)

/-- 元の全 necklace の生成射を同じ Day 圏で読む。 -/
def necklaceCubicalDayCell {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    necklaceCubicalDay.obj T.necklace ⟶ necklaceCubicalDayMapping K x y :=
  .mk (necklaceCubicalCell T)

/-- 元の一点から来る単位射を同じ Day 圏で読む。 -/
def necklaceCubicalDayIdentity (K : SSet.{u}) (x : K _⦋0⦌) :
    𝟙_ CubicalDaySet.{u} ⟶ necklaceCubicalDayMapping K x x :=
  .mk (necklaceCubicalIdentity K x)

/-- 元の mapping object 全体の合成を同じ Day 圏で読む。 -/
def necklaceCubicalDayCompose (K : SSet.{u}) (x y z : K _⦋0⦌) :
    necklaceCubicalDayMapping K x y ⊗ necklaceCubicalDayMapping K y z ⟶
      necklaceCubicalDayMapping K x z :=
  .mk (necklaceCubicalCompose K x y z)

/-- Day 圏での生成射は元の生成射そのもの。 -/
lemma necklaceCubicalDayCell_natTrans {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) : (necklaceCubicalDayCell T).natTrans = necklaceCubicalCell T := rfl

/-- Day 圏での単位は元の単位射そのもの。 -/
lemma necklaceCubicalDayIdentity_natTrans (K : SSet.{u}) (x : K _⦋0⦌) :
    (necklaceCubicalDayIdentity K x).natTrans = necklaceCubicalIdentity K x := rfl

/-- Day 圏での合成は元の合成射そのもの。 -/
lemma necklaceCubicalDayCompose_natTrans (K : SSet.{u}) (x y z : K _⦋0⦌) :
    (necklaceCubicalDayCompose K x y z).natTrans = necklaceCubicalCompose K x y z := rfl

/-- 元の一点の生成射と強モノイダル単位は、同じ Day 圏の単位射を回収する。 -/
lemma necklaceCubicalDayIdentity_unit (K : SSet.{u}) (x : K _⦋0⦌) :
    necklaceCubicalDayIdentity K x =
      Functor.LaxMonoidal.ε necklaceCubicalDay.{u} ≫ necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) :=
  DayFunctor.hom_ext (necklaceCubicalIdentity_unit K x)

/-- 元の両生成射の tensor と実合成は、元の強モノイダル比較と wedge を回収する。 -/
lemma necklaceCubicalDayCompose_cell {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (necklaceCubicalDayCell T ⊗ₘ necklaceCubicalDayCell U) ≫
        necklaceCubicalDayCompose K x y z =
      Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace U.necklace ≫
        necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) :=
  DayFunctor.hom_ext (necklaceCubicalCompose_cell K x y z T U)

/-- 元の全可換三角形による生成射の関係式を、同じ Day 圏で読む。 -/
lemma necklaceCubicalDayCell_relation {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U) :
    necklaceCubicalDay.map f.necklaceHom ≫ necklaceCubicalDayCell U =
      necklaceCubicalDayCell T :=
  DayFunctor.hom_ext (necklaceCubicalCell_relation f)

/-- 元の全 necklace 図式を同じ Day 圏で読む。 -/
def necklaceCubicalDayDiagram (K : SSet.{u}) (x y : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y ⥤ CubicalDaySet.{u} :=
  necklaceCubicalDiagram K x y ⋙ cubicalDayEquivalence.inverse

/-- 元の mapping object と全生成射の余錐を、同じ Day 圏で読む。 -/
def necklaceCubicalDayCocone (K : SSet.{u}) (x y : K _⦋0⦌) :
    Cocone (necklaceCubicalDayDiagram K x y) :=
  cubicalDayEquivalence.inverse.mapCocone (colimit.cocone (necklaceCubicalDiagram K x y))

/-- 元の mapping object は、同じ Day 圏でも全 necklace 図式の余極限。 -/
def necklaceCubicalDayIsColimit (K : SSet.{u}) (x y : K _⦋0⦌) :
    IsColimit (necklaceCubicalDayCocone K x y) :=
  isColimitOfPreserves cubicalDayEquivalence.inverse
    (colimit.isColimit (necklaceCubicalDiagram K x y))

end SerrePositivity.KST.SConstruction
