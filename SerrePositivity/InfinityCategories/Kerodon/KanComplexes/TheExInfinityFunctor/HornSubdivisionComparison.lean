module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionNerveChains

/-!
# horn の細分から面の nerve への比較

概要：horn の単体の面の像を horn 内の面として表し、細分から面の nerve への写像を作る。
方針：各単体の欠けた頂点は全ての部分面にも欠けることを使い、sd⊣Ex で転置する。
規約：Moss 2020 Proposition 21 の境界条件の実際の horn への移行。
使われ方：二重細分の horn 上での制限の計算。

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
概要：horn の単体の頂点写像を ulift した単調写像として表す。
方針：標準単体の asOrderHom を両側で ULift に持ち上げる。
規約：細分の有限鎖の頂点の宇宙と合わせる。
使われ方：horn の単体に沿った面の像。
-/
def hornSimplexOrderHom (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategory)
    (s : (SSet.horn.{u} n k).obj (op d)) :
    ULift.{u} (Fin (d.len + 1)) →o ULift.{u} (Fin (n + 1)) where
  toFun i := ULift.up (SSet.stdSimplex.asOrderHom s.val i.down)
  monotone' _ _ h := (SSet.stdSimplex.asOrderHom s.val).monotone h

/--
概要：horn の単体の非空な部分面の像も horn に属する。
方針：元の単体の欠けた頂点が、頂点集合の像にも欠けていることを示す。
規約：horn の像の頂点集合による定義を使う。
使われ方：面の像を horn の面の部分型へ制限する。
-/
theorem hornSimplexOrderHom_map_mem (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategory)
    (s : (SSet.horn.{u} n k).obj (op d))
    (C : NonemptyFiniteChains (ULift.{u} (Fin (d.len + 1)))) :
    HornFaceSet n k (C.map (hornSimplexOrderHom n k d s)) := by
  have hs := (SSet.mem_horn_iff k s.val).mp s.property
  obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem _).mp hs
  refine ⟨j, ?_, ?_⟩
  · exact fun h => hj (Or.inr (Set.mem_singleton_iff.mpr h))
  · intro hm
    obtain ⟨i, _, hi⟩ := (NonemptyFiniteChains.mem_map_iff C (hornSimplexOrderHom n k d s) _).mp hm
    apply hj
    exact Or.inl ⟨i.down, congrArg ULift.down hi⟩

/--
概要：horn の単体に沿って面の有限鎖を horn 内の面へ送る単調写像。
方針：頂点の像の有限鎖に、証明済みの horn 条件を付ける。
規約：horn の細分の各標準単体での比較。
使われ方：horn から面の nerve の Ex への写像。
-/
def hornSimplexFaceMap (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategory)
    (s : (SSet.horn.{u} n k).obj (op d)) :
    NonemptyFiniteChains (ULift.{u} (Fin (d.len + 1))) →o HornFacePoset.{u} n k where
  toFun C := ⟨C.map (hornSimplexOrderHom n k d s), hornSimplexOrderHom_map_mem n k d s C⟩
  monotone' _C _D h := (NonemptyFiniteChains.orderHomMap (hornSimplexOrderHom n k d s)).monotone h

/--
概要：horn からその面の nerve の Ex への比較。
方針：各単体に沿った面の像に nerve を適用し、単体の前合成と像の合成を合わせる。
規約：sd⊣Ex による horn の細分比較の随伴形。
使われ方：実際の細分された horn から面の nerve への写像。
-/
def hornFacesExUnit (n : ℕ) (k : Fin (n + 1)) :
    (SSet.horn.{u} n k : SSet.{u}) ⟶ SSet.ex.obj (nerve (HornFacePoset.{u} n k)) where
  app d := ↾fun s => ULift.up (nerveMap (hornSimplexFaceMap n k d.unop s).monotone.functor)
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply NatTrans.ext
    funext a
    apply ConcreteCategory.hom_ext
    intro t
    apply nerve.ext_of_isThin
    funext i
    let F : ULift.{u} (Fin (e.unop.len + 1)) →o ULift.{u} (Fin (d.unop.len + 1)) :=
      { toFun j := ULift.up (f.unop j.down)
        monotone' _ _ h := f.unop.toOrderHom.monotone h }
    change hornSimplexFaceMap n k e.unop ((SSet.horn n k).toFunctor.map f s) (t.obj i) =
      hornSimplexFaceMap n k d.unop s ((t.obj i).map F)
    apply Subtype.ext
    change (t.obj i).map (hornSimplexOrderHom n k e.unop ((SSet.horn n k).toFunctor.map f s)) =
      ((t.obj i).map F).map (hornSimplexOrderHom n k d.unop s)
    rw [finiteChainMap_comp]
    rfl

/--
概要：実際の horn の細分から horn の面の nerve への比較写像。
方針：各単体の面の像で作った Ex への比較を随伴同値で転置する。
規約：二重細分の境界条件の比較。
使われ方：有限鎖の nerve 上の一致を元の horn の細分へ戻す。
-/
def hornSubdivisionComparison (n : ℕ) (k : Fin (n + 1)) :
    SSet.sd.obj (SSet.horn.{u} n k) ⟶ nerve (HornFacePoset.{u} n k) :=
  (SSet.sdExAdjunction.homEquiv _ _).symm (hornFacesExUnit n k)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
