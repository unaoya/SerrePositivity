module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap

/-! # 終対象間の任意の辺の同型性

概要：二つの終対象の間のどの辺も、辺のホモトピー類の圏で同型である。
方針：A2 の片側逆射の構成を二回使い、与えられた辺の両側逆射を得る。
規約：HTT §1.2.12・§1.2.13。使われ方：任意の錐から標準 fiber への比較辺の同型性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory SSet.Truncated
open scoped _root_.Simplicial

/-- 概要：終対象間の指定された辺を順射とするホモトピー圏の同型。
方針：片側逆射を二回作り、二つの片側逆射の式から逆向きの合成式も得る。
規約：HTT §1.2.12、quasicategory の仮定。使われ方：選択した比較辺そのものの同型性を示す。 -/
def terminalEdgeIso {X : SSet.{u}} [SSet.Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y)
    (f : Edge (X := (SSet.truncation 2).obj X) x y) :
    HomotopyCategory₂.mk (A := (SSet.truncation 2).obj X) x ≅ HomotopyCategory₂.mk y := by
  let sg := Classical.choice (hx.nonempty_split f)
  let g := sg.1
  let sk := Classical.choice (hy.nonempty_split g)
  let k := sk.1
  have hg : HomotopyCategory₂.homMk f ≫ HomotopyCategory₂.homMk g = 𝟙 _ :=
    sg.2.homotopyCategory₂_fac
  have hk : HomotopyCategory₂.homMk g ≫ HomotopyCategory₂.homMk k = 𝟙 _ :=
    sk.2.homotopyCategory₂_fac
  have hf : HomotopyCategory₂.homMk f = HomotopyCategory₂.homMk k := by
    calc
      _ = HomotopyCategory₂.homMk f ≫
          (HomotopyCategory₂.homMk g ≫ HomotopyCategory₂.homMk k) := by rw [hk, Category.comp_id]
      _ = (HomotopyCategory₂.homMk f ≫ HomotopyCategory₂.homMk g) ≫
          HomotopyCategory₂.homMk k := (Category.assoc _ _ _).symm
      _ = HomotopyCategory₂.homMk k := by rw [hg, Category.id_comp]
  exact ⟨HomotopyCategory₂.homMk f, HomotopyCategory₂.homMk g, hg, by rw [hf]; exact hk⟩

/-- 概要：終対象間の任意の辺のホモトピー類は同型射。
方針：与えた辺を順射とする同型を取り出す。
規約：HTT §1.2.12。使われ方：極限錐の間の比較辺を同型射として射影する。 -/
lemma isIso_homMk_of_terminal {X : SSet.{u}} [SSet.Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y)
    (f : Edge (X := (SSet.truncation 2).obj X) x y) :
    IsIso (HomotopyCategory₂.homMk f) := by
  change IsIso (terminalEdgeIso hx hy f).hom
  infer_instance

/-- 概要：辺の終点を等しい零単体に沿って移す。
方針：終点の等式の消去を使う。
規約：HTT §1.2.3。使われ方：標準錐の頂点を標準 fiber の頂点に同定する。 -/
def edgeTransportTarget {X : SSet.{u}} {x y z : X _⦋0⦌} (h : y = z)
    (f : Edge (X := (SSet.truncation 2).obj X) x y) :
    Edge (X := (SSet.truncation 2).obj X) x z := h ▸ f

/-- 概要：終点の同定に沿う辺の移送は、そのホモトピー類の同型性を保つ。
方針：終点の等式を消去する。
規約：HTT §1.2.3。使われ方：fiber への比較辺の終点を実際の標準 fiber に合わせる。 -/
lemma isIso_homMk_edgeTransportTarget {X : SSet.{u}} [SSet.Quasicategory X]
    {x y z : X _⦋0⦌} (h : y = z) (f : Edge (X := (SSet.truncation 2).obj X) x y)
    (hf : IsIso (HomotopyCategory₂.homMk f)) :
    IsIso (HomotopyCategory₂.homMk (edgeTransportTarget h f)) := by
  cases h
  exact hf

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
