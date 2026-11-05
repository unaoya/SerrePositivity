module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceAssociatorAugmentation
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceUnitorAugmentation

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
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の necklace 同型と augmentation の可換性から、K 内の実同型を得る。 -/
def necklaceInIso {K : SSet.{u}} {x y : K _⦋0⦌} {T U : NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) : T ≅ U where
  hom := ⟨e.hom, h⟩
  inv :=
    { necklaceHom := e.inv
      w := ((necklaceSimplicialSet.mapIso e).eq_inv_comp.mpr h).symm }
  hom_inv_id := NecklaceInHom.ext e.hom_inv_id
  inv_hom_id := NecklaceInHom.ext e.inv_hom_id

/-- K 内の実同型の正方向は、指定した元の necklace 同型そのもの。 -/
lemma necklaceInIso_hom {K : SSet.{u}} {x y : K _⦋0⦌} {T U : NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) :
    (necklaceInIso e h).hom.necklaceHom = e.hom := rfl

/-- K 内の実同型の逆方向も、指定した元の necklace 同型そのもの。 -/
lemma necklaceInIso_inv {K : SSet.{u}} {x y : K _⦋0⦌} {T U : NecklaceIn K x y}
    (e : T.necklace ≅ U.necklace) (h : e.hom.map ≫ U.map = T.map) :
    (necklaceInIso e h).inv.necklaceHom = e.inv := rfl

/-- 固定端点の三重連結の、K 内の元の実結合同型。 -/
def necklaceInAssociator {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : NecklaceIn K w x) (U : NecklaceIn K x y) (V : NecklaceIn K y z) :
    necklaceInWedge (necklaceInWedge T U) V ≅ necklaceInWedge T (necklaceInWedge U V) :=
  necklaceInIso (necklaceAssociator T.necklace U.necklace V.necklace)
    (necklaceInAssociator_augmentation T U V)

/-- 固定端点の一点 necklace を左に貼る、K 内の元の実単位同型。 -/
def necklaceInLeftUnitor {K : SSet.{u}} {x y : K _⦋0⦌} (T : NecklaceIn K x y) :
    necklaceInWedge (necklaceInPoint K x) T ≅ T :=
  necklaceInIso (necklaceLeftUnitor T.necklace) (necklaceInLeftUnitor_augmentation T)

/-- 固定端点の一点 necklace を右に貼る、K 内の元の実単位同型。 -/
def necklaceInRightUnitor {K : SSet.{u}} {x y : K _⦋0⦌} (T : NecklaceIn K x y) :
    necklaceInWedge T (necklaceInPoint K y) ≅ T :=
  necklaceInIso (necklaceRightUnitor T.necklace) (necklaceInRightUnitor_augmentation T)

/-- K 内の実結合同型は、元の native necklace の結合同型を回収する。 -/
lemma necklaceInAssociator_hom {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : NecklaceIn K w x) (U : NecklaceIn K x y) (V : NecklaceIn K y z) :
    (necklaceInAssociator T U V).hom.necklaceHom =
      (necklaceAssociator T.necklace U.necklace V.necklace).hom := rfl

/-- K 内の実左単位は、元の native necklace の左単位を回収する。 -/
lemma necklaceInLeftUnitor_hom {K : SSet.{u}} {x y : K _⦋0⦌} (T : NecklaceIn K x y) :
    (necklaceInLeftUnitor T).hom.necklaceHom = (necklaceLeftUnitor T.necklace).hom := rfl

/-- K 内の実右単位は、元の native necklace の右単位を回収する。 -/
lemma necklaceInRightUnitor_hom {K : SSet.{u}} {x y : K _⦋0⦌} (T : NecklaceIn K x y) :
    (necklaceInRightUnitor T).hom.necklaceHom = (necklaceRightUnitor T.necklace).hom := rfl

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInAssociator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInAssociator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator_hom := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInAssociator_hom

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso_hom := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso_inv := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso_inv

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInLeftUnitor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInLeftUnitor := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInLeftUnitor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInLeftUnitor_hom := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInLeftUnitor_hom

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInRightUnitor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInRightUnitor := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInRightUnitor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInRightUnitor_hom := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInRightUnitor_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInIso._proof_3
