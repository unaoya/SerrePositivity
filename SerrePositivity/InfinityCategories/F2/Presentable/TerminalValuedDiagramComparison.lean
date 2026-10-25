module

public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero

/-!
概要：全頂点が終対象である図式同士を全関手同型で比較する。
方針：点ごとの終対象性から全関手圏内の終対象性を構成し、その一意性を使う。
規約：頂点同型の族だけでなく全関手の可逆二胞体を返す。
使われ方：交互可算図式の奇数部分列と固定標的の定値図式の全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：終対象値の二つの全図式の間の関手同型。
方針：全関手圏の終対象性の境界充填と終対象の一意性を使う。
規約：全高次を含む FunctorIso を返す。
使われ方：固定標的への可算交互比較。 -/
def terminalValuedDiagramIso {K C : SSet.{u}} [Quasicategory C] (F G : K ⟶ C)
    (hF : ∀ k, IsTerminalVertex (F.app (Opposite.op ⦋0⦌) k))
    (hG : ∀ k, IsTerminalVertex (G.app (Opposite.op ⦋0⦌) k)) : FunctorIso F G :=
  terminalVertexIso (isTerminalVertex_functorVertex_of_pointwise F hF)
    (isTerminalVertex_functorVertex_of_pointwise G hG)

/-- 概要：終対象値の全図式と定値終対象図式の間の関手同型。
方針：定値図式も点ごとに終対象であることから全関手終対象性を使う。
規約：任意の添字 K と元の指定終対象 t を使う。
使われ方：奇数部分列を元の固定標的に縮約する。 -/
def terminalValuedDiagramConstantIso {K C : SSet.{u}} [Quasicategory C] (F : K ⟶ C)
    (hF : ∀ k, IsTerminalVertex (F.app (Opposite.op ⦋0⦌) k))
    (t : C _⦋0⦌) (ht : IsTerminalVertex t) : FunctorIso F (SSet.const t) :=
  terminalValuedDiagramIso F (SSet.const t) hF (fun _ ↦ by
    change IsTerminalVertex (PinchedHom.constant t 0)
    rw [pinchedConstant_zero]
    exact ht)

end SerrePositivity.InfinityCategories.F2.Presentable
