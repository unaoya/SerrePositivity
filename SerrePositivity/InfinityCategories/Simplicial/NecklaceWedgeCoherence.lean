module
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeStructureNaturality

/-! # 元の necklace の wedge の五角と三角
概要：元の結合・左右単位の構造同型が coherent なモノイダル法則を満たす。
方針：元の tensor 射による対象等号の保存と eqToHom の合成則を使う。
規約：元の単体的構造射を変更しない。使われ方：native necklace モノイダル圏。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、全四つの necklace について五角を満たす。 -/
lemma necklaceAssociator_pentagon (W X Y Z : Necklace.{u}) :
    necklaceWedgeMap (necklaceAssociator W X Y).hom (𝟙 Z) ≫
        (necklaceAssociator W (necklaceWedge X Y) Z).hom ≫
          necklaceWedgeMap (𝟙 W) (necklaceAssociator X Y Z).hom =
      (necklaceAssociator (necklaceWedge W X) Y Z).hom ≫
        (necklaceAssociator W X (necklaceWedge Y Z)).hom := by
  simp only [necklaceAssociator, eqToIso.hom, ← eqToHom_refl,
    necklaceWedgeMap_eqToHom, eqToHom_trans]

/-- 元の結合同型と一点の左右単位は、全 necklace について三角を満たす。 -/
lemma necklaceAssociator_triangle (X Y : Necklace.{u}) :
    (necklaceAssociator X necklacePoint Y).hom ≫
        necklaceWedgeMap (𝟙 X) (necklaceLeftUnitor Y).hom =
      necklaceWedgeMap (necklaceRightUnitor X).hom (𝟙 Y) := by
  simp only [necklaceAssociator, necklaceLeftUnitor, necklaceRightUnitor, eqToIso.hom,
    ← eqToHom_refl, necklaceWedgeMap_eqToHom, eqToHom_trans]

end SerrePositivity.KST.SConstruction
