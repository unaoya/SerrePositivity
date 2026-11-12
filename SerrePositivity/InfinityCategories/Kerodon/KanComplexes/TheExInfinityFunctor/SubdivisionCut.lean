module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertex

/-!
# 細分の複雑度を切る冪等作用素

概要：Moss の j_n^k を非空有限集合の単調写像として構成する。
方針：最大元が k 以下なら集合を保ち、それ以外では同じ最大元の初期区間に置き換える。
規約：Moss 2020 Definition 23。Segal 1974 Proposition 1.6 の対角模型の補助。
使われ方：X→Ex(X) の anodyne 性に用いる単体の複雑度フィルター。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：有限鎖は、その最大元以下の初期区間に含まれる。
方針：各元が最大元以下であることを使う。
規約：Moss 2020 Definition 23 の単調性の補助。
使われ方：複雑度を切る作用素の構成。
-/
theorem finiteChain_le_initialSegment (n : ℕ)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    s ≤ finiteChainInitialSegment n (finiteChainMaximum s) := by
  intro i hi
  simp only [finiteChainInitialSegment, OrderHom.coe_mk, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Finset.le_max' s.finset i hi

/--
概要：最大元を閾値と比較し、必要な場合だけ初期区間にする作用素。
方針：最大元以下の範囲に留まるように集合を拡大する。
規約：Moss 2020 Definition 23 の j_n^k の頂点上の定義。
使われ方：細分の nerve の冪等な自己写像。
-/
def finiteChainCut (n : ℕ) (k : ULift.{u} (Fin (n + 1))) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) →o
      NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  toFun s := if finiteChainMaximum s ≤ k then s
    else finiteChainInitialSegment n (finiteChainMaximum s)
  monotone' a b hab := by
    have hm := finiteChainMaximum.monotone hab
    by_cases ha : finiteChainMaximum a ≤ k
    · by_cases hb : finiteChainMaximum b ≤ k
      · simp only [ha, hb, ↓reduceIte]
        exact hab
      · simp only [ha, hb, ↓reduceIte]
        exact hab.trans (finiteChain_le_initialSegment n b)
    · have hb : ¬ finiteChainMaximum b ≤ k := fun hb => ha (hm.trans hb)
      simp only [ha, hb, ↓reduceIte]
      exact (finiteChainInitialSegment n).monotone hm

/--
概要：複雑度を切る作用素は最大元を保つ。
方針：初期区間の最大元の計算を使う。
規約：Moss 2020 Definition 23 の j_n^k。
使われ方：作用素の合成則と冪等性。
-/
theorem finiteChainCut_maximum (n : ℕ) (k : ULift.{u} (Fin (n + 1)))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainMaximum (finiteChainCut n k s) = finiteChainMaximum s := by
  dsimp only [finiteChainCut, OrderHom.coe_mk]
  split_ifs
  · rfl
  · exact finiteChainMaximum_initialSegment n _

/--
概要：閾値 k≤l の二つの作用素の合成は小さい閾値の作用素に等しい。
方針：最大元は変わらないため、閾値との比較だけで場合分けする。
規約：Moss 2020 Definition 23 の j_n^k∘j_n^l=j_n^k。
使われ方：複雑度フィルターの包含と冪等性。
-/
theorem finiteChainCut_comp (n : ℕ) (k l : ULift.{u} (Fin (n + 1))) (hkl : k ≤ l)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainCut n k (finiteChainCut n l s) = finiteChainCut n k s := by
  change (if finiteChainMaximum (finiteChainCut n l s) ≤ k then finiteChainCut n l s
    else finiteChainInitialSegment n (finiteChainMaximum (finiteChainCut n l s))) = _
  rw [finiteChainCut_maximum]
  by_cases h : finiteChainMaximum s ≤ k
  · have hl := h.trans hkl
    simp only [h, ↓reduceIte, finiteChainCut, OrderHom.coe_mk, hl]
  · simp only [h, ↓reduceIte, finiteChainCut, OrderHom.coe_mk]

/--
概要：複雑度を切る作用素は冪等である。
方針：同じ閾値の合成則を使う。
規約：Moss 2020 Definition 23。
使われ方：像と固定点の一致。
-/
theorem finiteChainCut_idempotent (n : ℕ) (k : ULift.{u} (Fin (n + 1))) :
    ∀ s, finiteChainCut n k (finiteChainCut n k s) = finiteChainCut n k s :=
  fun s => finiteChainCut_comp n k k le_rfl s

/--
概要：最大の閾値における作用素は恒等である。
方針：すべての頂点が最後の頂点以下である。
規約：Moss 2020 Definition 23 の j_n^n=id。
使われ方：有限の複雑度フィルターが全単体を尽くすこと。
-/
theorem finiteChainCut_last (n : ℕ)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainCut n (ULift.up (Fin.last n)) s = s := by
  change (if finiteChainMaximum s ≤ ULift.up (Fin.last n) then s else _) = s
  rw [ite_eq_left (show finiteChainMaximum s ≤ ULift.up (Fin.last n) from Fin.le_last _)]

/--
概要：閾値零の作用素は最大元の初期区間を取る写像である。
方針：最大元が零なら元の集合自体がその初期区間に一致する。
規約：Moss 2020 Definition 23 の j_n^0。
使われ方：X の Ex への像を複雑度零の固定点と同定する。
-/
theorem finiteChainCut_zero (n : ℕ)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainCut n (ULift.up 0) s = finiteChainInitialSegment n (finiteChainMaximum s) := by
  dsimp only [finiteChainCut, OrderHom.coe_mk]
  split_ifs with h
  · apply le_antisymm (finiteChain_le_initialSegment n s)
    intro i hi
    have him : i ≤ finiteChainMaximum s := (Finset.mem_filter.mp hi).2
    have hmi : finiteChainMaximum s ≤ i := h.trans (show ULift.up (0 : Fin (n + 1)) ≤ i from
      Fin.zero_le i.down)
    have he : i = finiteChainMaximum s := le_antisymm him hmi
    exact he ▸ Finset.max'_mem s.finset s.nonempty
  · rfl

/--
概要：細分された標準単体の複雑度を k で切る写像。
方針：有限鎖の単調な作用素に nerve を適用する。
規約：Moss 2020 Definition 23 の j_n^k。
使われ方：Ex の各次数の固定点フィルター。
-/
def subdivisionCutAt (n : SimplexCategory) (k : Fin (n.len + 1)) :
    SimplexCategory.sd.{u}.obj n ⟶ SimplexCategory.sd.obj n :=
  nerveMap (finiteChainCut.{u} n.len (ULift.up k)).monotone.functor

/--
概要：細分の切断作用素の合成は小さい閾値の作用素になる。
方針：nerve の各頂点で有限鎖の合成則を使う。
規約：Moss 2020 Definition 23。射の合成では l を先に適用する。
使われ方：固定点フィルターの包含。
-/
@[reassoc] theorem subdivisionCutAt_comp (n : SimplexCategory) (k l : Fin (n.len + 1))
    (hkl : k ≤ l) :
    subdivisionCutAt.{u} n l ≫ subdivisionCutAt n k = subdivisionCutAt n k := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact finiteChainCut_comp n.len (ULift.up k) (ULift.up l) hkl (s.obj i)

/--
概要：細分の切断作用素は冪等である。
方針：同じ閾値の合成則を使う。
規約：Moss 2020 Definition 23。
使われ方：固定点と作用素の像の同定。
-/
@[reassoc] theorem subdivisionCutAt_idempotent (n : SimplexCategory) (k : Fin (n.len + 1)) :
    subdivisionCutAt.{u} n k ≫ subdivisionCutAt n k = subdivisionCutAt n k :=
  subdivisionCutAt_comp n k k le_rfl

/--
概要：最大閾値の細分作用素は恒等射である。
方針：各頂点で有限鎖の最後の閾値の式を使う。
規約：Moss 2020 Definition 23 の j_n^n=id。
使われ方：複雑度の有限性。
-/
theorem subdivisionCutAt_last (n : SimplexCategory) :
    subdivisionCutAt.{u} n (Fin.last n.len) = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact finiteChainCut_last n.len (s.obj i)

/--
概要：閾値零の細分作用素は最終頂点写像とその切断の合成である。
方針：各頂点で初期区間を取る式を比較する。
規約：Moss 2020 Definition 23 の j_n^0。
使われ方：複雑度零の固定点と X の Ex への像の同定。
-/
theorem subdivisionCutAt_zero (n : SimplexCategory) :
    subdivisionCutAt.{u} n 0 = subdivisionLastVertexAt n ≫ subdivisionVertexSectionAt n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact finiteChainCut_zero n.len (s.obj i)

/--
概要：複雑度を切る写像は最終頂点写像を保つ。
方針：有限鎖の最大元が変わらないことを各頂点で使う。
規約：Moss 2020 Definition 23。
使われ方：Ex の単位の像がすべての複雑度で固定されること。
-/
@[reassoc] theorem subdivisionCutAt_lastVertex (n : SimplexCategory) (k : Fin (n.len + 1)) :
    subdivisionCutAt.{u} n k ≫ subdivisionLastVertexAt n = subdivisionLastVertexAt n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg ULift.down (finiteChainCut_maximum n.len (ULift.up k) (s.obj i))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
