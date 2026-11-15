module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingMonad
public import SerrePositivity.InfinityCategories.HA.Monads.EndofunctorComposition

/-!
概要：walking monad の全単体作用として coherent なモナドの型を固定する。
方針：N(Δ₊) から全自己関手単体集合への単体写像と、指定単位・順序和の保存を用いる。
規約：h Fun 上の通常のモナドではなく、全次元の単体作用をデータに持つ。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の誘導モナドとその代数の共通入力。
walking monad の表示は Riehl–Verity, Homotopy coherent adjunctions and the formal
 theory of monads, Remark 3.3.8 の有限順序集合と順序和による表示。
Kerodon Remark 6.2.1.4（Tag 02EN）のホモトピー双圏へ忘却する前の作用を保持する。
随伴からこの全作用を構成する存在定理は別途必要であり、ここでは仮定しない。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking monad から自己関手準圏への全coherentな作用。
方針：全単体写像に、空順序集合と順序和を保存する法則を課す。
規約：全作用が構造のデータであり、存在やモナド性を述べる命題の束ではない。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の全誘導モナドの標的。 -/
structure NativeMonad (C : SSet.{u}) where
  /-- N(Δ₊) の全単体の作用。頂点・辺だけに切り詰めない。 -/
  action : WalkingMonadShape.{u} ⟶ EndofunctorSpace C
  /-- 空順序集合が指定された恒等自己関手に作用する法則。 -/
  map_unit : walkingMonadUnit ≫ action = endofunctorUnit C
  /-- 全順序和の作用が同じ全関手の合成と一致する法則。 -/
  map_composition : walkingMonadComposition ≫ action =
    (action ⊗ₘ action) ≫ endofunctorComposition C

namespace NativeMonad

variable {C : SSet.{u}}

/-- 概要：全作用が一致する二つのモナド構造は一致する。
方針：残る二つの欄の証明非依存性を使う。規約：台の準圏は固定。
使われ方：HA §4.7.2 の同じ全作用の照合。 -/
@[ext] lemma ext {T T' : NativeMonad C} (h : T.action = T'.action) : T = T' := by
  cases T
  cases T'
  cases h
  rfl

/-- 概要：一点順序集合の作用から元の自己関手を取り出す。
方針：全関手単体集合の零単体を curry と単位の表示で戻す。
規約：h Fun での同型類ではなく実際の単体写像。
使われ方：HA Proposition 4.7.3.3 の underlying endofunctor。 -/
def endofunctor (T : NativeMonad C) : C ⟶ C :=
  curryHomEquiv'.symm ((SSet.unitHomEquiv _).symm
    (T.action.app (Opposite.op ⦋0⦌) walkingMonadGenerator))

/-- 概要：元の自己関手の単位からの表示は同じ一点順序集合の作用。
方針：curry の表示の両逆を使う。規約：全関手単体集合への射として比較する。
使われ方：HA Proposition 4.7.3.3 の指定自己関手の検収。 -/
lemma curry_endofunctor (T : NativeMonad C) :
    curry' T.endofunctor = (SSet.unitHomEquiv _).symm
      (T.action.app (Opposite.op ⦋0⦌) walkingMonadGenerator) :=
  (curryHomEquiv' (X := C) (Y := C)).apply_symm_apply _

/-- 概要：自己関手の零単体は元の一点順序集合の作用と一致する。
方針：単位からの表示の同値の両逆を使う。規約：同じ作用の零単体。
使われ方：HA Proposition 4.7.3.3 の元の合成関手との照合。 -/
lemma endofunctor_vertex (T : NativeMonad C) :
    SSet.unitHomEquiv _ (curry' T.endofunctor) =
      T.action.app (Opposite.op ⦋0⦌) walkingMonadGenerator := by
  rw [curry_endofunctor]
  exact (SSet.unitHomEquiv _).apply_symm_apply _

end NativeMonad

end SerrePositivity.InfinityCategories.HA.Monads
