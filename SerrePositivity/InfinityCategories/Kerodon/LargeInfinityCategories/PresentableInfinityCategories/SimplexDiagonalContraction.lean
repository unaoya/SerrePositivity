module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplexPrefix
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleContractionSpan
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：反対単体圏の二項対角の各 comma を明示的に収縮する。
方針：全作用素に最小頂点を加え、恒等関手と零頂点の定値関手へ自然変換を与える。
規約：宇宙を合わせた元の反対単体圏を使う。
使われ方：幾何学的実現の添字の sifted 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：宇宙を合わせた反対単体圏。
方針：対象と射を元の小さい宇宙へ持ち上げる。
規約：単体作用素を変更しない。
使われ方：幾何学的実現の小さい添字。 -/
abbrev SmallSimplexOpposite := ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)

/-- 概要：同じ反対単体次数の二項対角関手。
方針：対象と射を二重に取る。
規約：元の二項直積の圏を使う。
使われ方：sifted 性の comma 判定。 -/
def simplexDegreeDiagonal : SmallSimplexOpposite.{u} ⥤
    SmallSimplexOpposite.{u} × SmallSimplexOpposite.{u} where
  obj n := (n, n)
  map f := (f, f)

/-- 概要：対角の指定 comma における零次数の最小頂点。
方針：零単体から二つの指定単体の最小頂点へ送る。
規約：指定した二つの次数を保持する。
使われ方：comma の収縮の定値先。 -/
def simplexDiagonalZero (m n : SmallSimplexOpposite.{u}) :
    StructuredArrow (m, n) simplexDegreeDiagonal :=
  StructuredArrow.mk (Y := ULiftHom.objUp (ULift.up (Opposite.op ⦋0⦌)))
    (ULift.up (SimplexCategory.const ⦋0⦌ m.objDown.down.unop 0).op,
      ULift.up (SimplexCategory.const ⦋0⦌ n.objDown.down.unop 0).op)

/-- 概要：comma の対象の始域単体へ新しい最小頂点を加える。
方針：二つの単体作用素の零頂点を同時に延長する。
規約：二つの固定された終域単体を変更しない。
使われ方：comma の収縮関手の対象。 -/
def simplexDiagonalPrefixObj {m n : SmallSimplexOpposite.{u}}
    (a : StructuredArrow (m, n) simplexDegreeDiagonal) :
    StructuredArrow (m, n) simplexDegreeDiagonal :=
  StructuredArrow.mk
    (Y := ULiftHom.objUp (ULift.up (Opposite.op ⦋a.right.objDown.down.unop.len + 1⦌)))
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.1.down.unop).op,
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.2.down.unop).op)

/-- 概要：最小頂点を追加する操作の comma の射への作用。
方針：元の作用素の両端へ最小頂点を加え、合成公式で三角形を保つ。
規約：元の指定射を使う。
使われ方：comma の収縮関手。 -/
def simplexDiagonalPrefixMap {m n : SmallSimplexOpposite.{u}}
    {a b : StructuredArrow (m, n) simplexDegreeDiagonal} (f : a ⟶ b) :
    simplexDiagonalPrefixObj a ⟶ simplexDiagonalPrefixObj b :=
  StructuredArrow.homMk (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap f.right.down.unop).op) (by
    apply Prod.ext
    · have h := congrArg (fun t ↦ t.1.down.unop) f.w
      change f.right.down.unop ≫ a.hom.1.down.unop = b.hom.1.down.unop at h
      change ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap f.right.down.unop ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.1.down.unop).op) =
          ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone b.hom.1.down.unop).op
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap_comp_cone, h]
    · have h := congrArg (fun t ↦ t.2.down.unop) f.w
      change f.right.down.unop ≫ a.hom.2.down.unop = b.hom.2.down.unop at h
      change ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap f.right.down.unop ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.2.down.unop).op) =
          ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone b.hom.2.down.unop).op
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap_comp_cone, h])

/-- 概要：最小頂点を追加する comma の収縮関手。
方針：対象と射の明示構成に恒等・合成の座標公式を適用する。
規約：全ての面と退化を含める。
使われ方：恒等関手と定値関手への収縮の共通始域。 -/
def simplexDiagonalPrefix (m n : SmallSimplexOpposite.{u}) :
    StructuredArrow (m, n) simplexDegreeDiagonal ⥤
      StructuredArrow (m, n) simplexDegreeDiagonal where
  obj := simplexDiagonalPrefixObj
  map := simplexDiagonalPrefixMap
  map_id a := by
    apply StructuredArrow.hom_ext
    change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap (𝟙 a.right.objDown.down.unop)).op = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap_id]
    rfl
  map_comp f g := by
    apply StructuredArrow.hom_ext
    change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap (g.right.down.unop ≫ f.right.down.unop)).op = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap_comp]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
