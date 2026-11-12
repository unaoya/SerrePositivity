module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertex

/-!
# 順序集合の nerve と有限鎖への細分比較

概要：順序集合の nerve の細分から、非空有限鎖の順序集合の nerve への写像を構成する。
方針：各単体の有限鎖の像を取り、sd⊣Ex の随伴で転置する。
規約：Moss 2020 Proposition 21 の Kan 性の準備。一般の B 関手の構成は仮定しない。
使われ方：二重細分された horn の頂点を有限鎖で計算する。

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
概要：順序集合の nerve の単体を、ulift した頂点からの単調写像として表す。
方針：単体の関手の対象写像と、射から得る不等式を使う。
規約：sd の頂点の宇宙と揃えて ULift を使う。
使われ方：単体に沿った有限鎖の像。
-/
def nerveSimplexOrderHom {P : Type u} [PartialOrder P] (n : SimplexCategory)
    (s : (nerve P).obj (op n)) : ULift.{u} (Fin (n.len + 1)) →o P where
  toFun i := s.obj i.down
  monotone' _ _ h := leOfHom (s.map (homOfLE h))

/--
概要：有限鎖の像を二度取ることは単調写像の合成の像を取ることに等しい。
方針：有限集合の二重の像を一つの像へまとめる。
規約：細分比較の自然性に必要な有限鎖の関手性。
使われ方：Ex の単体の自然性の検証。
-/
theorem finiteChainMap_comp {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P →o Q) (g : Q →o R) (s : NonemptyFiniteChains P) :
    (s.map f).map g = s.map (g.comp f) := by
  classical
  apply NonemptyFiniteChains.ext
  simp only [NonemptyFiniteChains.map, Finset.image_image]
  rfl

/--
概要：各 nerve の単体から、非空有限鎖の nerve の Ex の単体を作る。
方針：単体を表す単調写像による有限鎖の像に nerve を適用する。
規約：Moss 2020 Proposition 21 の二重細分に用いる比較の随伴形。
使われ方：細分から有限鎖への比較写像の転置前の構成。
-/
def nerveChainsExUnit (P : Type u) [PartialOrder P] :
    nerve P ⟶ SSet.ex.obj (nerve (NonemptyFiniteChains P)) where
  app n := ↾fun s => ULift.up (nerveMap
    (NonemptyFiniteChains.orderHomMap (nerveSimplexOrderHom n.unop s)).monotone.functor)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro t
    apply nerve.ext_of_isThin
    funext i
    let F : ULift.{u} (Fin (m.unop.len + 1)) →o ULift.{u} (Fin (n.unop.len + 1)) :=
      { toFun j := ULift.up (f.unop j.down)
        monotone' _ _ h := f.unop.toOrderHom.monotone h }
    change (t.obj i).map (nerveSimplexOrderHom m.unop ((nerve P).map f s)) =
      ((t.obj i).map F).map (nerveSimplexOrderHom n.unop s)
    rw [finiteChainMap_comp]
    rfl

/--
概要：順序集合の nerve の細分から非空有限鎖の nerve への比較。
方針：有限鎖の像で作った Ex への写像を sd⊣Ex で転置する。
規約：Moss 2020 Proposition 21 の準備。同型性は主張しない。
使われ方：二重細分された horn の有限鎖による表示。
-/
def subdivisionNerveChains (P : Type u) [PartialOrder P] :
    SSet.sd.obj (nerve P) ⟶ nerve (NonemptyFiniteChains P) :=
  (SSet.sdExAdjunction.homEquiv _ _).symm (nerveChainsExUnit P)

/--
概要：有限鎖の像で構成した Ex への写像は、順序集合の単調写像に関して自然である。
方針：各単体と各鎖で有限鎖の像の合成則を使う。
規約：細分比較の関手性。
使われ方：horn の部分順序集合への制限と細分比較の整合。
-/
theorem nerveChainsExUnit_naturality {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) :
    nerveMap f.monotone.functor ≫ nerveChainsExUnit Q =
      nerveChainsExUnit P ≫ SSet.ex.map
        (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro t
  apply nerve.ext_of_isThin
  funext i
  change (t.obj i).map (nerveSimplexOrderHom n.unop
      ((nerveMap f.monotone.functor).app n s)) =
    ((t.obj i).map (nerveSimplexOrderHom n.unop s)).map f
  rw [finiteChainMap_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
