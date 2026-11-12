module

public import SerrePositivity.KST.Comparison.MatrixSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
# 単体的環の加法による基点の平行移動

概要：任意の零次の元を、全次数の退化を引く単体的同型によって零へ移す。
方針：零次への一意な射と加法の自然性を使って同型を構成する。
規約：KST Lemma 2.13 の単位行列から零行列への基点移動。乗法逆元は使わない。
使われ方：行列の正次数のホモトピー群を零基点の係数群で表示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：零次の元の各次数への完全な退化。
方針：標準単体から零単体への一意な射を作用させる。
規約：加法と減法の平行移動に用いる。
使われ方：任意の基点を零へ送る単体的同型。
-/
def ringDegenerateVertex (A : SimplicialObject RingCat.{u}) (a : A.obj (op ⦋0⦌))
    (n : ℕ) : A.obj (op ⦋n⦌) :=
  (A.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op).hom a

/--
概要：零次の元の完全退化は全ての面・退化と可換する。
方針：零単体への一意な射の合成則を使う。
規約：単体圏の射は任意。
使われ方：平行移動の自然性。
-/
theorem ringDegenerateVertex_natural (A : SimplicialObject RingCat.{u})
    (a : A.obj (op ⦋0⦌)) {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    (A.map f.op).hom (ringDegenerateVertex A a n) = ringDegenerateVertex A a m := by
  change (A.map f.op).hom ((A.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op).hom a) = _
  rw [← RingCat.comp_apply, ← A.map_comp]
  rfl

/--
概要：零次の元の零次への退化は元の元に一致する。
方針：零単体上の定数射は恒等射である。
規約：基点の厳密な計算。
使われ方：平行移動での基点保存。
-/
theorem ringDegenerateVertex_zero (A : SimplicialObject RingCat.{u})
    (a : A.obj (op ⦋0⦌)) : ringDegenerateVertex A a 0 = a := by
  unfold ringDegenerateVertex
  rw [SimplexCategory.const_eq_id, op_id, A.map_id]
  rfl

/--
概要：元 a の完全退化を引いて零へ移す単体的な平行移動の同型。
方針：各次数の減法と加法を互いの逆とし、完全退化の自然性を使う。
規約：台単体集合の同型であり、環準同型とは主張しない。
使われ方：KST Lemma 2.13 の単位行列の基点の移動。
-/
def ringTranslationIso (A : SimplicialObject RingCat.{u}) (a : A.obj (op ⦋0⦌)) :
    ringSpace A ≅ ringSpace A :=
  NatIso.ofComponents (fun n => (show A.obj n ≃ A.obj n from
    { toFun := fun x => x - ringDegenerateVertex A a n.unop.len
      invFun := fun x => x + ringDegenerateVertex A a n.unop.len
      left_inv := fun x => sub_add_cancel x _
      right_inv := fun x => add_sub_cancel_right x _ }).toIso) (by
    intro m n f
    apply ConcreteCategory.hom_ext
    intro x
    let y : A.obj m := x
    change (A.map f).hom y - ringDegenerateVertex A a n.unop.len =
      (A.map f).hom (y - ringDegenerateVertex A a m.unop.len)
    rw [map_sub]
    have h : (A.map f).hom (ringDegenerateVertex A a m.unop.len) =
        ringDegenerateVertex A a n.unop.len := ringDegenerateVertex_natural A a f.unop
    exact congrArg (fun z => (A.map f).hom y - z) h.symm)

/--
概要：平行移動は指定した零次の元を零へ送る。
方針：零次の完全退化の計算と自己減法を使う。
規約：ホモトピー群の基点の等式として使う。
使われ方：零基点の群への比較。
-/
theorem ringTranslationIso_basepoint (A : SimplicialObject RingCat.{u})
    (a : A.obj (op ⦋0⦌)) :
    (ringTranslationIso A a).hom.app (op ⦋0⦌) a = (0 : A.obj (op ⦋0⦌)) := by
  change a - ringDegenerateVertex A a 0 = 0
  rw [ringDegenerateVertex_zero, sub_self]

/--
概要：任意の基点における単体的環の正次数の群と零基点の群の乗法同値。
方針：実際の平行移動の単体的同型を K-L9 の群の同型へ渡す。
規約：Kan 性は係数環の台集合に明示する。
使われ方：行列のホモトピー群の零基点の係数表示。
-/
def ringPositiveHomotopyBasepointEquiv (A : SimplicialObject RingCat.{u})
    [KanComplex (ringSpace A)] (a : A.obj (op ⦋0⦌)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n a ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (ringTranslationIso A a)
    (ringTranslationIso_basepoint A a)

end SerrePositivity.KST.Comparison
