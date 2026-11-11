module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornChainMissingVertex
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# 面の鎖の鎖から horn への写像

概要：二段階の非空有限鎖の nerve から horn への写像を構成する。
方針：候補頂点写像の nerve を標準単体へ送り、各単体が共通に避ける頂点で horn に制限する。
規約：Moss 2020 Proposition 21 の二重細分の horn の充填に向けた具体的な写像。
使われ方：細分比較と合成する horn への充填候補。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite PartialOrder
open scoped _root_.Simplicial

/--
概要：二段階の面の鎖の nerve から標準単体への候補写像。
方針：単調な候補頂点写像に nerve を適用して、標準単体との同型を合成する。
規約：二重細分の頂点の選び方を全ての単体へ拡張する。
使われ方：horn の部分複体への因子化。
-/
def hornChainToSimplex (n : ℕ) (k : Fin (n + 1)) :
    nerve (NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))) ⟶ Δ[n] :=
  nerveMap (hornChainVertex n k).monotone.functor ≫ (SSet.stdSimplex.isoNerve n).inv

/--
概要：正次元の標準単体への候補写像の像は k-horn に含まれる。
方針：各単体の最後の鎖を共通の上界として、候補頂点の全てが避ける頂点を選ぶ。
規約：二重細分の horn への包含の直接証明。
使われ方：標準単体への写像を horn に制限する。
-/
theorem hornChainToSimplex_range_le (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    SSet.Subcomplex.range (hornChainToSimplex.{u} n k) ≤ SSet.horn n k := by
  intro d x hx
  obtain ⟨t, rfl⟩ := hx
  apply (SSet.mem_horn_iff k _).mpr
  obtain ⟨j, hj, hm⟩ := hornChainVertex_common_missing n hn k (t.obj (Fin.last d.unop.len))
  intro he
  have hjmem : j ∈ Set.range (SSet.stdSimplex.asOrderHom
      ((hornChainToSimplex n k).app d t)) ∪ {k} := he.symm ▸ Set.mem_univ j
  rcases hjmem with ⟨i, hi⟩ | hjk
  · have hle : t.obj i ≤ t.obj (Fin.last d.unop.len) :=
      leOfHom (t.map (homOfLE (Fin.le_last i)))
    apply hm (t.obj i) hle
    apply ULift.ext
    change (hornChainVertex n k (t.obj i)).down = j at hi
    exact hi
  · exact hj (Set.mem_singleton_iff.mp hjk)

/--
概要：二段階の面の鎖の nerve から k-horn への写像。
方針：標準単体への候補を、証明した像の包含で horn に制限する。
規約：Moss 2020 Proposition 21 の二重細分の充填候補の値域。
使われ方：二重細分された標準単体から horn への写像の構成。
-/
def hornChainToHorn (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    nerve (NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))) ⟶
      SSet.horn n k :=
  SSet.Subcomplex.lift (hornChainToSimplex n k) (hornChainToSimplex_range_le n hn k)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
