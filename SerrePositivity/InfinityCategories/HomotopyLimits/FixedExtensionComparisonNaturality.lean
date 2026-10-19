module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionRestriction

/-!
概要：固定した初期図式を保つ制限は、可縮な延長空間の比較同型と実際の辺の類を保つ。
方針：制限先の延長空間の Hom の一意性を使い、同じ二頂点の比較を照合する。
規約：終点 fiber の任意の辺には主張しない。使われ方：三角形から長辺への比較の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 可縮な二空間の間の射は、同じ二頂点の指定比較同型を保つ。 -/
lemma contractibleVertexIso_map {X Y : SSet.{u}} (hX : IsContractibleKan X)
    (hY : IsContractibleKan Y) (f : X ⟶ Y) (x y : X _⦋0⦌) :
    VertexIso.map (hX.vertexIso x y) f = hY.vertexIso (f.app _ x) (f.app _ y) := by
  have := hY.kanComplex
  apply Iso.ext
  exact (hY.isTerminalVertex (f.app _ y)).isTerminalHo.hom_ext _ _

variable {K L D E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (β : K ⟶ B)
  (k : L ⟶ K) (j : D ⟶ L) (v : D ⟶ E) (hv : v ≫ p = (j ≫ k) ≫ β)
  (hK : leftAnodyneExtensions (j ≫ k)) (hL : leftAnodyneExtensions j)
local notation "S" => relativeFunctorExtensionSpace p β (j ≫ k) v hv
local notation "R" => fixedExtensionRestriction p β k j v hv

/-- 初期図式を保つ制限は、元の可縮な延長空間の比較同型を同じ制限先の比較へ写す。 -/
lemma fixedExtensionRestriction_vertexIso_map (x y : (S) _⦋0⦌) :
    VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p β (j ≫ k) hK v hv).vertexIso x y) R =
      (relativeFunctorExtensionSpace_isContractibleKan p (k ≫ β) j hL v
        (hv.trans (Category.assoc _ _ _))).vertexIso ((R).app _ x) ((R).app _ y) :=
  contractibleVertexIso_map
    (relativeFunctorExtensionSpace_isContractibleKan p β (j ≫ k) hK v hv)
    (relativeFunctorExtensionSpace_isContractibleKan p (k ≫ β) j hL v
      (hv.trans (Category.assoc _ _ _))) R x y

include hK in
/-- 元の延長空間の実際の辺を制限した類も、同じ制限先の二頂点の比較同型の射である。 -/
lemma fixedExtensionRestriction_edge_homMk {x y : (S) _⦋0⦌} (e : (S).Edge x y) :
    SSet.Truncated.HomotopyCategory.homMk (e.map R).toTruncated =
      ((relativeFunctorExtensionSpace_isContractibleKan p (k ≫ β) j hL v
        (hv.trans (Category.assoc _ _ _))).vertexIso ((R).app _ x) ((R).app _ y)).hom := by
  have hS := relativeFunctorExtensionSpace_isContractibleKan p β (j ≫ k) hK v hv
  have := hS.kanComplex
  have he : SSet.Truncated.HomotopyCategory.homMk e.toTruncated = (hS.vertexIso x y).hom :=
    (hS.isTerminalVertex y).isTerminalHo.hom_ext _ _
  have hr := congrArg (fun z : (SSet.HomotopyCategory.mk x : SSet.HomotopyCategory S) ⟶
    SSet.HomotopyCategory.mk y ↦ (SSet.mapHomotopyCategory R).map z) he
  exact hr.trans (congrArg Iso.hom
    (fixedExtensionRestriction_vertexIso_map p β k j v hv hK hL x y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
