module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornChainNerve

/-!
# horn の面の部分順序集合

概要：horn に属する非空面の順序集合と、その nerve から horn への最終頂点写像を構成する。
方針：欠けた頂点があるという条件で面の部分型を取り、各鎖の最大の面を使う。
規約：Moss 2020 Proposition 21 の二重細分の境界の計算。
使われ方：horn 上で候補写像が反復最終頂点に一致すること。

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
概要：k-horn に属する非空の面の順序集合。
方針：頂点の有限鎖に、k 以外に欠けた頂点がある条件を付ける。
規約：有限鎖の頂点集合は線形順序なので全ての非空な面を表す。
使われ方：horn の細分に対する比較の値域。
-/
def HornFacePoset (n : ℕ) (k : Fin (n + 1)) :=
  {s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) // HornFaceSet n k s}

/--
概要：horn の面の順序は元の面の包含から継承する。
方針：部分型の部分順序を使う。
規約：比較可能性は頂点集合の包含。
使われ方：horn の面の nerve と非空有限鎖。
-/
instance hornFacePoset_partialOrder (n : ℕ) (k : Fin (n + 1)) :
    PartialOrder (HornFacePoset.{u} n k) := inferInstanceAs (PartialOrder (Subtype _))

/--
概要：horn の面を全ての面の順序集合へ含める単調写像。
方針：部分型の値を取る。
規約：順序は継承した包含である。
使われ方：細分比較の自然性へ与える写像。
-/
def hornFaceInclusion (n : ℕ) (k : Fin (n + 1)) :
    HornFacePoset.{u} n k →o NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  toFun s := s.val
  monotone' _ _ h := h

/--
概要：horn の面の nerve を、それぞれの最大頂点で標準単体へ送る。
方針：面の包含と最大元の単調性に nerve を適用する。
規約：horn の細分の最終頂点写像の頂点による表示。
使われ方：horn への最終頂点の因子化。
-/
def hornFacesToSimplex (n : ℕ) (k : Fin (n + 1)) : nerve (HornFacePoset.{u} n k) ⟶ Δ[n] :=
  nerveMap ((finiteChainMaximum (α := ULift.{u} (Fin (n + 1)))).comp
    (hornFaceInclusion n k)).monotone.functor ≫ (SSet.stdSimplex.isoNerve n).inv

/--
概要：horn の面の nerve の最終頂点の像は horn に含まれる。
方針：鎖の最後の面の欠けた頂点を選び、全ての最大頂点もそこに属することを使う。
規約：境界写像の値域を元の horn に揃える。
使われ方：horn への最終頂点写像の定義。
-/
theorem hornFacesToSimplex_range_le (n : ℕ) (k : Fin (n + 1)) :
    SSet.Subcomplex.range (hornFacesToSimplex.{u} n k) ≤ SSet.horn n k := by
  intro d x hx
  obtain ⟨t, rfl⟩ := hx
  apply (SSet.mem_horn_iff k _).mpr
  obtain ⟨j, hj, hm⟩ := (t.obj (Fin.last d.unop.len)).property
  intro he
  have hjmem : j ∈ Set.range (SSet.stdSimplex.asOrderHom
      ((hornFacesToSimplex n k).app d t)) ∪ {k} := he.symm ▸ Set.mem_univ j
  rcases hjmem with ⟨i, hi⟩ | hjk
  · have hle : (t.obj i).val ≤ (t.obj (Fin.last d.unop.len)).val :=
      leOfHom (t.map (homOfLE (Fin.le_last i)))
    have hmem : finiteChainMaximum (t.obj i).val ∈ (t.obj (Fin.last d.unop.len)).val.finset :=
      hle (Finset.max'_mem (t.obj i).val.finset (t.obj i).val.nonempty)
    change (finiteChainMaximum (t.obj i).val).down = j at hi
    exact hm ((ULift.ext hi) ▸ hmem)
  · exact hj (Set.mem_singleton_iff.mp hjk)

/--
概要：horn の面の nerve から元の horn への最終頂点写像。
方針：標準単体への写像の像の包含で horn に制限する。
規約：二重細分の境界条件に現れる写像。
使われ方：細分比較と Ex の単位を horn 内で比較する。
-/
def hornFacesLastVertex (n : ℕ) (k : Fin (n + 1)) :
    nerve (HornFacePoset.{u} n k) ⟶ SSet.horn n k :=
  SSet.Subcomplex.lift (hornFacesToSimplex n k) (hornFacesToSimplex_range_le n k)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
