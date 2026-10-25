module

public import SerrePositivity.InfinityCategories.Core.JoinAssociator
public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociator

/-!
概要：Core と HomotopyLimits の join の結合同型を比較する。
方針：切断表示と三つの区間の和表示を各次数で同定する。
規約：三因子は任意で、空区間も含める。既存の定義は変更しない。
使われ方：P-13 の二重 coslice の再結合の供給。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：切断表示を左右の区間長による和表示へ移す。
方針：切断と残りの長さを読み、二つの単体を保持する。
規約：頂点数零も含む。使われ方：二つの再結合の表示の比較。 -/
def stableAugJoinToSum (K L : SSet.{u}) (r : ℕ)
    (s : StableAugJoin K L r) : HomotopyLimits.joinSumSimplex K L r :=
  ⟨⟨s.1.val, r - s.1.val, s.2.1, s.2.2⟩, by have := s.1.isLt; dsimp only; omega⟩

/-- 概要：join の和表示は切断表示の区間長を読み取ったものである。
方針：頂点数零と非零に分けて定義を比較する。
規約：補った空単体も含む。
使われ方：二つの結合同型の共通表示への移送。 -/
lemma augmentedJoinSumEquiv_eq_stable (K L : SSet.{u}) (r : ℕ)
    (s : Join.augObj (join K L) r) :
    HomotopyLimits.augmentedJoinSumEquiv K L r s =
      stableAugJoinToSum K L r (stableAugJoinEquiv K L r s) := by
  cases r <;> rfl

/-- 概要：Core の再結合は HomotopyLimits の三つの区間の表示を保つ。
方針：二つの切断を展開し、右側の復号公式で三因子を比較する。
規約：頂点数零を含む任意の三因子。
使われ方：結合同型の各単体での一致。 -/
lemma stableAugJoinAssociatorEquiv_tripleEncoding (K L M : SSet.{u}) (r : ℕ)
    (s : Join.augObj (join (join K L) M) r) :
    HomotopyLimits.rightJoinTripleEncoding K L M r
      (stableAugJoinAssociatorEquiv K L M r s) =
        HomotopyLimits.leftJoinTripleEncoding K L M r s := by
  change HomotopyLimits.rightJoinSumTripleEquiv K L M r
      (HomotopyLimits.augmentedJoinSumEquiv K (join L M) r
        (stableAugJoinAssociatorEquiv K L M r s)) =
    HomotopyLimits.leftJoinSumTripleEquiv K L M r
      (HomotopyLimits.augmentedJoinSumEquiv (join K L) M r s)
  rw [augmentedJoinSumEquiv_eq_stable, augmentedJoinSumEquiv_eq_stable]
  simp only [stableAugJoinAssociatorEquiv, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  simp only [stableAugJoinToSum, HomotopyLimits.rightJoinSumTripleEquiv,
    HomotopyLimits.leftJoinSumTripleEquiv, Equiv.coe_fn_mk]
  rw [augmentedJoinSumEquiv_eq_stable, augmentedJoinSumEquiv_eq_stable]
  simp only [stableAugJoinToSum]
  let t := stableAugJoinEquiv (join K L) M r s
  let ab := stableAugJoinEquiv K L t.1.val t.2.1
  have hd := stableAugReassociation_right_decode K L M r t
  have hb : (stableAugJoinEquiv L M (r - ab.1.val)
      (stableAugReassociationEquiv K L M r t).2.2).1.val = t.1.val - ab.1.val :=
    congrArg (fun z : StableAugJoin L M (r - ab.1.val) ↦ z.1.val) hd
  apply HomotopyLimits.joinTripleSimplex_ext
  · rfl
  · exact hb
  · change r - ab.1.val - (stableAugJoinEquiv L M (r - ab.1.val)
      (stableAugReassociationEquiv K L M r t).2.2).1.val = r - t.1.val
    rw [hb]
    have := t.1.isLt
    have := ab.1.isLt
    omega
  · rfl
  · exact stableAugJoin_left_heq hd
  · exact (stableAugJoin_right_heq hd).trans (cast_heq _ _)

/-- 概要：Core と HomotopyLimits の結合同型の順方向の射は一致する。
方針：各単体を共通の三つの区間表示で比較する。
規約：三因子に仮定は置かない。
使われ方：二つの再結合を使う証明間の書き換え。 -/
lemma stableJoinAssociator_hom_eq_joinAssociator (K L M : SSet.{u}) :
    (stableJoinAssociator K L M).hom = (HomotopyLimits.joinAssociator K L M).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (HomotopyLimits.rightJoinTripleEncoding K L M (n + 1)).injective
  change HomotopyLimits.rightJoinTripleEncoding K L M (n + 1)
    (stableAugJoinAssociatorEquiv K L M (n + 1) s) =
      HomotopyLimits.rightJoinTripleEncoding K L M (n + 1)
        ((HomotopyLimits.rightJoinTripleEncoding K L M (n + 1)).symm
          (HomotopyLimits.leftJoinTripleEncoding K L M (n + 1) s))
  rw [Equiv.apply_symm_apply]
  exact stableAugJoinAssociatorEquiv_tripleEncoding K L M (n + 1) s

/-- 概要：二つの join の結合同型は同型そのものとして一致する。
方針：順方向の射の一致を同型の外延性へ渡す。
規約：任意の三因子を扱う。
使われ方：逆方向も含む結合同型の移送。 -/
lemma stableJoinAssociator_eq_joinAssociator (K L M : SSet.{u}) :
    stableJoinAssociator K L M = HomotopyLimits.joinAssociator K L M := by
  apply Iso.ext
  exact stableJoinAssociator_hom_eq_joinAssociator K L M

/-- 概要：末尾の二因子が点である場合も二つの再結合の射は一致する。
方針：一般の三因子の比較を特殊化する。
規約：K に仮定は置かない。
使われ方：P-13 の反復 coslice の比較。 -/
lemma stableJoinAssociator_hom_eq_joinAssociator_point_point (K : SSet.{u}) :
    (stableJoinAssociator K Δ[0] Δ[0]).hom =
      (HomotopyLimits.joinAssociator K Δ[0] Δ[0]).hom :=
  stableJoinAssociator_hom_eq_joinAssociator K Δ[0] Δ[0]

end SerrePositivity.InfinityCategories.F2.Presentable
