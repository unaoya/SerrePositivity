module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceAssociatorAugmentation
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceUnitorAugmentation

/-! # K 内の固定端点 necklace の実構造同型
概要：元の結合と一点の左右単位を、K への augmentation を保つ同型へ持ち上げる。
方針：元の necklace 同型と厳密な可換条件から、逆向きも K 内の可換三角形にする。
規約：全単体的写像を保持。使われ方：cubical 余極限の合成の結合・単位則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の necklace 同型と augmentation の可換性から、K 内の実同型を得る。 -/
def necklaceInIso {K : SSet.{u}} {x y : K _⦋0⦌} {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) : T ≅ U where
  hom := ⟨e.hom, h⟩
  inv :=
    { necklaceHom := e.inv
      w := ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplicialSet.mapIso e).eq_inv_comp.mpr h).symm }
  hom_inv_id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext e.hom_inv_id
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext e.inv_hom_id

/-- K 内の実同型の正方向は、指定した元の necklace 同型そのもの。 -/
lemma necklaceInIso_hom {K : SSet.{u}} {x y : K _⦋0⦌} {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInIso e h).hom.necklaceHom = e.hom := rfl

/-- K 内の実同型の逆方向も、指定した元の necklace 同型そのもの。 -/
lemma necklaceInIso_inv {K : SSet.{u}} {x y : K _⦋0⦌} {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInIso e h).inv.necklaceHom = e.inv := rfl

/-- 固定端点の三重連結の、K 内の元の実結合同型。 -/
def necklaceInAssociator {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T.necklace U.necklace V.necklace)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator_augmentation T U V)

/-- 固定端点の一点 necklace を左に貼る、K 内の元の実単位同型。 -/
def necklaceInLeftUnitor {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) T ≅ T :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T.necklace) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor_augmentation T)

/-- 固定端点の一点 necklace を右に貼る、K 内の元の実単位同型。 -/
def necklaceInRightUnitor {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y) ≅ T :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T.necklace) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor_augmentation T)

/-- K 内の実結合同型は、元の native necklace の結合同型を回収する。 -/
lemma necklaceInAssociator_hom {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator T U V).hom.necklaceHom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T.necklace U.necklace V.necklace).hom := rfl

/-- K 内の実左単位は、元の native necklace の左単位を回収する。 -/
lemma necklaceInLeftUnitor_hom {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor T).hom.necklaceHom = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T.necklace).hom := rfl

/-- K 内の実右単位は、元の native necklace の右単位を回収する。 -/
lemma necklaceInRightUnitor_hom {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor T).hom.necklaceHom = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T.necklace).hom := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
