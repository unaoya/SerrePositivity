module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft

/-!
概要：coslice 射影の頂点上の fiber と左 pinched 写像空間の同型。
方針：fiber の標準単体表示を、反転した右 pinched 単体へ移す。
規約：任意の単体集合で成立する厳密な同型として構成する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、Construction 5.5.2.1（Tag 01ZW）、unstraightening の fiber 比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右 pinched 単体の最終頂点の反転は最初の頂点。
方針：単体圏の射を唯一の入力頂点で評価する。
規約：反転は単体圏の共変な involution。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左 pinched 単体の始点条件。 -/
lemma rev_lastVertex (n : ℕ) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (Fin.last (n + 1)).rev = 0
  exact Fin.rev_last _

/-- 概要：右 pinched 単体の先頭面の反転は零番目の面。
方針：先頭面を最終頂点を飛ばす面と書き、反転の面の式を使う。
規約：n 次の面から n+1 次の単体への包含。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左 pinched 単体の定値面。 -/
lemma rev_front (n : ℕ) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) = SimplexCategory.δ 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, SimplexCategory.rev_map_δ, Fin.rev_last]

/-- 概要：定値単体は単体集合の反転で同じ定値単体に対応する。
方針：零単体への射は一意であることを使う。
規約：反転後の頂点は opObjEquiv の逆で指定する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、反転した固定面の比較。 -/
lemma constant_opObjEquiv {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n := by
  change X.map (SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op x = _
  congr 2

/-- 概要：左右を反転した終点固定延長は始点固定延長。
方針：最初の頂点と後続の頂点で反転の式を計算する。
規約：左右の pinched 模型のパラメータの反転を同時に行う。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber との自然性。 -/
lemma rev_extend_rev {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.rev.map α)) =
      SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  induction i using Fin.cases with
  | zero =>
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.rev.map α).toOrderHom
      (0 : Fin (m + 2)).rev).rev = 0
    rw [Fin.rev_zero]
    exact (congrArg Fin.rev (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last
      (m := m) (n := n) (SimplexCategory.rev.map α).toOrderHom)).trans (Fin.rev_last _)
  | succ i =>
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.rev.map α).toOrderHom
      i.succ.rev).rev = (α.toOrderHom i).succ
    rw [Fin.rev_succ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, Fin.rev_castSucc,
      SimplexCategory.rev_map_apply, Fin.rev_rev, Fin.rev_rev]
    rfl

/-- 概要：左 pinched 単体の型は coslice fiber の固定条件を持つ単体の型と同値。
方針：反転した右 pinched 単体の二つの固定条件を元の単体集合で読む。
規約：ここでは各次数の同値を述べ、自然性は別に確認する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、coslice fiber の単体の回収。 -/
def leftPinchedSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n} where
  toFun s := by
    let t := SSet.opObjEquiv s
    refine ⟨SSet.opObjEquiv t.val, ?_, ?_⟩
    · have h := congrArg SSet.opObjEquiv t.target
      change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n)).op
        (SSet.opObjEquiv t.val) = x at h
      rw [rev_lastVertex] at h
      exact h
    · have h := congrArg SSet.opObjEquiv t.source
      change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n)).op
        (SSet.opObjEquiv t.val) = SSet.opObjEquiv
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm y) n) at h
      rw [rev_front, constant_opObjEquiv] at h
      exact h
  invFun s := SSet.opObjEquiv.symm
    { val := SSet.opObjEquiv.symm s.val
      source := by
        apply SSet.opObjEquiv.injective
        change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n)).op s.val =
          SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm y) n)
        rw [rev_front, constant_opObjEquiv]
        exact s.property.2
      target := by
        apply SSet.opObjEquiv.injective
        change X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n)).op s.val = x
        rw [rev_lastVertex]
        exact s.property.1 }
  left_inv s := by
    apply SSet.opObjEquiv.injective
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rfl
  right_inv s := by apply Subtype.ext; rfl

/-- 概要：coslice 射影の頂点 fiber は左 pinched 写像空間と同型。
方針：二つの単体の同値を合成し、始点固定延長の自然性を確認する。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、空間値 unstraightening の fiber 表示。 -/
noncomputable def cosliceFiberPinchedLeftIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y d.unop.len).trans
      (leftPinchedSimplexEquiv x y d.unop.len).symm)) (by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.opObjEquiv.injective
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    apply SSet.opObjEquiv.injective
    dsimp only [Equiv.toIso, Equiv.trans, Equiv.symm, leftPinchedSimplexEquiv,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex m
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y).map α s) =
        X.map (SimplexCategory.rev.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend
          (SimplexCategory.rev.map α.unop))).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n s)
    rw [rev_extend_rev]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex_naturality α.unop s)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
