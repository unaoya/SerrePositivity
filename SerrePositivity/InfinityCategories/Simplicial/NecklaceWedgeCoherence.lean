module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeStructureNaturality

/-! # 元の necklace の wedge の五角と三角
概要：元の結合・左右単位の構造同型が coherent なモノイダル法則を満たす。
方針：元の tensor 射による対象等号の保存と eqToHom の合成則を使う。
規約：元の単体的構造射を変更しない。使われ方：native necklace モノイダル圏。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、全四つの necklace について五角を満たす。 -/
lemma necklaceAssociator_pentagon (W X Y Z : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator W X Y).hom (𝟙 Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator W (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedge X Y) Z).hom ≫
          _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap (𝟙 W) (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator X Y Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedge W X) Y Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator W X (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedge Y Z)).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator, eqToIso.hom, ← eqToHom_refl,
    _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_eqToHom, eqToHom_trans]

/-- 元の結合同型と一点の左右単位は、全 necklace について三角を満たす。 -/
lemma necklaceAssociator_triangle (X Y : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator X _root_.SerrePositivity.InfinityCategories.Simplicial.necklacePoint Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap (𝟙 X) (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceLeftUnitor Y).hom =
      _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceRightUnitor X).hom (𝟙 Y) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator, _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceLeftUnitor, _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceRightUnitor, eqToIso.hom,
    ← eqToHom_refl, _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceWedgeMap_eqToHom, eqToHom_trans]

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_pentagon := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator_pentagon

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_triangle := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceAssociator_triangle
