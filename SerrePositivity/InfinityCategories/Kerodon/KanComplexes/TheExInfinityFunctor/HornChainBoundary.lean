module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset

/-!
# 有限鎖の horn 上の境界条件

概要：horn の面の鎖に制限すると、二重細分の候補は最大元による最終頂点に一致する。
方針：全ての面が horn 内であることを有限鎖の像の所属で確認する。
規約：Moss 2020 Proposition 21 の境界条件の有限鎖の nerve 上の形。
使われ方：二重細分の horn 上の制限の計算。

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
概要：horn の面の鎖を全ての面の鎖へ送った際の候補頂点は反復最大元である。
方針：像の全ての面の horn 条件と、最大元の単調写像との交換を使う。
規約：二重細分の境界条件の頂点上の式。
使われ方：有限鎖の nerve 上の境界の一致。
-/
theorem hornChainVertex_map_hornFaces (n : ℕ) (k : Fin (n + 1))
    (C : NonemptyFiniteChains (HornFacePoset.{u} n k)) :
    hornChainVertex n k (C.map (hornFaceInclusion n k)) =
      finiteChainMaximum (finiteChainGreatest C).val := by
  have hC : ∀ s ∈ (C.map (hornFaceInclusion n k)).finset, HornFaceSet n k s := by
    intro s hs
    obtain ⟨t, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff C (hornFaceInclusion n k) s).mp hs
    exact t.property
  rw [hornChainVertex_of_all_faces n k _ hC, finiteChainGreatest_map]
  rfl

/--
概要：horn 内の面の鎖の nerve に制限した候補写像は、通常の最終頂点の合成である。
方針：horn の包含の単射性で標準単体へ移し、各頂点で反復最大元の式を使う。
規約：Moss 2020 Proposition 21 の境界条件の中間形。
使われ方：二重細分された horn への制限の検証。
-/
@[reassoc] theorem hornChainToHorn_boundary (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    nerveMap (NonemptyFiniteChains.orderHomMap (hornFaceInclusion.{u} n k)).monotone.functor ≫
      hornChainToHorn n hn k =
    nerveMap (finiteChainGreatest (P := HornFacePoset.{u} n k)).monotone.functor ≫
      hornFacesLastVertex n k := by
  apply (cancel_mono (SSet.horn n k).ι).mp
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro t
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (hornChainVertex n k ((t.obj i).map (hornFaceInclusion n k))).down =
    (finiteChainMaximum (finiteChainGreatest (t.obj i)).val).down
  exact congrArg ULift.down (hornChainVertex_map_hornFaces n k (t.obj i))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
