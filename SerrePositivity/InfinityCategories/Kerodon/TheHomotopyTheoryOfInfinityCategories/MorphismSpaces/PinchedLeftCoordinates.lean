module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberCoordinates

/-!
概要：既存の左 pinched 写像空間を固定頂点・固定面の座標で記述する。
方針：右模型の二重の反転を添字写像で計算し、coslice fiber の座標と合わせる。
規約：Core の pinchedHomLeft の定義は変更しない。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、Construction 5.5.2.1（Tag 01ZW）、fiber と写像空間の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：先頭面の包含の反転は最初の面の包含。
方針：先頭面を最終面として表し、面の反転の公式を使う。
規約：反転前に除く頂点は最後、反転後は最初。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、右模型の定値面を左模型に移す。 -/
lemma pinchedFront_rev (n : ℕ) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) = SimplexCategory.δ 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, SimplexCategory.rev_map_δ, Fin.rev_last]

/-- 概要：最後の頂点を取る写像の反転は最初の頂点を取る写像。
方針：反転した順序写像を各頂点で評価する。
規約：始域は零次元。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、右模型の固定終点を左模型の固定始点にする。 -/
lemma pinchedLastVertex_rev (n : ℕ) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (Fin.last (n + 1)).rev = 0
  exact Fin.rev_last _

/-- 概要：反転した添字写像の最終点固定延長を反転すると最初の点固定延長。
方針：最初の頂点と後続頂点に分け、反転と castSucc・succ の交換を計算する。
規約：prependOrderHom は Core の錐の添字の規約を使う。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左模型の単体的構造と coslice の整合性。 -/
lemma pinchedExtend_rev {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.rev.map α)) =
      SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.rev.map α).toOrderHom
      (0 : Fin (m + 2)).rev).rev = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom 0
    rw [Fin.rev_zero]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]
    rw [Fin.rev_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom_zero]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.rev.map α).toOrderHom i.succ.rev).rev =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom i.succ
    rw [Fin.rev_succ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, Fin.rev_castSucc,
      SimplexCategory.rev_map_apply, Fin.rev_rev, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom_succ, Fin.rev_rev]
    rfl

/-- 概要：反転した単体集合の定値単体を戻すと元の定値単体。
方針：零次元への写像は反転しても唯一の写像であることを使う。
規約：任意の単体集合と全次数で成り立つ。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左模型の定値面の比較。 -/
lemma pinchedConstant_opObjEquiv {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n := by
  change X.map (SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op x = _
  have hc : SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) =
      SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [hc]
  rfl

/-- 概要：左 pinched 写像空間の n 単体の元の (n+1) 単体。
方針：パラメータと元の単体集合の二つの反転の同値を戻す。
規約：元の単体の頂点順序は左模型の向き。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の座標との照合。 -/
def pinchedLeftSimplexVal {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌) : X _⦋n + 1⦌ :=
  SSet.opObjEquiv (SSet.opObjEquiv s).val

/-- 概要：左 pinched 単体の最初の頂点は指定した始点。
方針：右模型の終点条件を単体集合の反転の下で計算する。
規約：最初の頂点を選ぶ射は定値零の写像。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice の固定端点の条件。 -/
lemma pinchedLeftSimplexVal_source {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (pinchedLeftSimplexVal n s) = x := by
  have h := congrArg SSet.opObjEquiv (SSet.opObjEquiv s).target
  change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n)).op
    (pinchedLeftSimplexVal n s) = x at h
  rwa [pinchedLastVertex_rev] at h

/-- 概要：左 pinched 単体の最初の面は終点に定値。
方針：右模型の先頭面の条件を反転し、定値単体の反転を計算する。
規約：固定される面は δ 0。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の射影の条件。 -/
lemma pinchedLeftSimplexVal_target {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌) :
    X.δ 0 (pinchedLeftSimplexVal n s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n := by
  have h := congrArg SSet.opObjEquiv (SSet.opObjEquiv s).source
  change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n)).op
    (pinchedLeftSimplexVal n s) = _ at h
  rw [pinchedFront_rev, pinchedConstant_opObjEquiv] at h
  exact h

/-- 概要：固定頂点と定値面のある単体を既存の左 pinched 単体に戻す。
方針：単体を反転し、始点と面の条件を右模型の終点と先頭面の条件に移す。
規約：二つの反転は Core の定義のまま使う。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber から既存の左模型への構成。 -/
def pinchedLeftSimplexInverse {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := X.op) (SSet.opObjEquiv.symm y)
    (SSet.opObjEquiv.symm x)).op _⦋n⦌
  refine SSet.opObjEquiv.symm
    { val := SSet.opObjEquiv.symm t.val, source := ?_, target := ?_ }
  · apply SSet.opObjEquiv.injective
    change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n)).op t.val = _
    rw [pinchedFront_rev, pinchedConstant_opObjEquiv]
    exact t.property.2
  · apply SSet.opObjEquiv.injective
    change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n)).op t.val = x
    rw [pinchedLastVertex_rev]
    exact t.property.1

/-- 概要：左 pinched 単体は元の (n+1) 単体によって一意に決まる。
方針：二つの反転の単射性と右模型の単体の外延性を使う。
規約：固定条件は命題なので証明の選択を区別しない。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左模型への自然性の証明。 -/
lemma pinchedLeftSimplexVal_injective {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ) :
    Function.Injective (pinchedLeftSimplexVal (x := x) (y := y) n) := by
  intro s t h
  apply SSet.opObjEquiv.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact SSet.opObjEquiv.injective h

/-- 概要：左 pinched 単体と固定頂点・固定面のある単体の座標は同値。
方針：反転を戻す写像とその逆を組にし、元の単体で両合成を比較する。
規約：coslice の座標と同一の固定条件を用いる。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の全次数の比較。 -/
def pinchedLeftSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n} where
  toFun s := ⟨pinchedLeftSimplexVal n s,
    pinchedLeftSimplexVal_source n s, pinchedLeftSimplexVal_target n s⟩
  invFun := pinchedLeftSimplexInverse n
  left_inv s := pinchedLeftSimplexVal_injective n rfl
  right_inv s := Subtype.ext rfl

/-- 概要：左 pinched 単体の座標は最初の頂点を固定する延長による引き戻しに自然。
方針：二つの反転の下で添字写像の延長を計算する。
規約：任意の面・退化を一つの式で扱う。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber との単体集合の同型。 -/
lemma pinchedLeftSimplexVal_naturality {X : SSet.{u}} {x y : X _⦋0⦌}
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal m ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y).map α.op s) =
      X.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)).op
        (pinchedLeftSimplexVal n s) := by
  change X.map
    (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.rev.map α))).op
      (pinchedLeftSimplexVal n s) = _
  rw [pinchedExtend_rev]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
