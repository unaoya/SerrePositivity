module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportRank

/-!
概要：edgewise の延長領域の外の頂点集合の対の全単射。
方針：最小の左添字に対応する右頂点の有無で分け、挿入と削除を互いに逆にする。
規約：この段階では頂点集合を対にし、非退化単体への移送は別に行う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーン接合の pairing のデータ。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：延長領域の外にある有限頂点集合の型。
方針：領域外の条件を部分型として保持する。
規約：領域外の証明は最小左添字を選ぶために使う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の分割前の頂点集合。 -/
def EdgewiseOutsideSupport (n : ℕ) :=
  {S : Finset (Fin (n + n + 1 + 1)) // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S}

/-- 概要：選んだ右頂点を欠く領域外の頂点集合の型。
方針：最小左添字の相方の不在を部分型で指定する。
規約：pairing の小さい方、型 II に対応する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーンで欠ける面の索引。 -/
def EdgewiseLowerSupport (n : ℕ) :=
  {S : EdgewiseOutsideSupport n // _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val S.property) ∉ S.val}

/-- 概要：選んだ右頂点を含む領域外の頂点集合の型。
方針：最小左添字の相方の存在を部分型で指定する。
規約：pairing の大きい方、型 I に対応する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、接合するホーンの全単体の索引。 -/
def EdgewiseUpperSupport (n : ℕ) :=
  {S : EdgewiseOutsideSupport n // _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val S.property) ∈ S.val}

/-- 概要：小さい方の頂点集合に選んだ右頂点を挿入して大きい方へ写す。
方針：挿入で領域外の条件と最小左添字が保たれることを使う。
規約：元の左頂点は存在するので挿入則が適用できる。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の順方向。 -/
def edgewiseSupportRaise {n : ℕ} (S : EdgewiseLowerSupport n) : EdgewiseUpperSupport n := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_mem S.val.val S.val.property
  have ht : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) S.val.val) := by
    intro h
    exact S.val.property ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportInDomain_insert_right_iff S.val.val i hi).1 h)
  let T : EdgewiseOutsideSupport n := ⟨insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) S.val.val, ht⟩
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot T.val T.property = i := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_eq_of_leftSupport_eq T.val S.val.val T.property S.val.property
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftSupport_insert_right S.val.val i)
  refine ⟨T, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot T.val T.property) ∈
    insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) S.val.val
  rw [hp]
  exact Finset.mem_insert_self _ _

/-- 概要：大きい方の頂点集合から選んだ右頂点を削除して小さい方へ写す。
方針：削除で領域外の条件と最小左添字が保たれることを使う。
規約：削除する右頂点は元の集合に含まれる。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の逆方向。 -/
def edgewiseSupportLower {n : ℕ} (S : EdgewiseUpperSupport n) : EdgewiseLowerSupport n := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_mem S.val.val S.val.property
  have ht : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n (S.val.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)) := by
    intro h
    exact S.val.property ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportInDomain_erase_right_iff S.val.val i hi).1 h)
  let T : EdgewiseOutsideSupport n := ⟨S.val.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i), ht⟩
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot T.val T.property = i := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_eq_of_leftSupport_eq T.val S.val.val T.property S.val.property
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftSupport_erase_right S.val.val i)
  refine ⟨T, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot T.val T.property) ∉
    S.val.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)
  rw [hp]
  exact Finset.notMem_erase _ _

/-- 概要：右頂点を挿入した後も選ぶ左添字は同じ。
方針：挿入による左添字集合の不変性を使う。
規約：証明の部分型は証明無関連性で同定する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、挿入・削除の往復の計算。 -/
lemma edgewiseSupportRaise_pivot {n : ℕ} (S : EdgewiseLowerSupport n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot (edgewiseSupportRaise S).val.val (edgewiseSupportRaise S).val.property =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_eq_of_leftSupport_eq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftSupport_insert_right _ _

/-- 概要：右頂点を削除した後も選ぶ左添字は同じ。
方針：削除による左添字集合の不変性を使う。
規約：証明の部分型は証明無関連性で同定する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、削除・挿入の往復の計算。 -/
lemma edgewiseSupportLower_pivot {n : ℕ} (S : EdgewiseUpperSupport n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot (edgewiseSupportLower S).val.val (edgewiseSupportLower S).val.property =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_eq_of_leftSupport_eq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftSupport_erase_right _ _

/-- 概要：領域外の小さい頂点集合と大きい頂点集合は全単射で対になる。
方針：挿入・削除で選ぶ左添字が変わらないことと有限集合の往復の法則を使う。
規約：全単射の順方向は一頂点の挿入。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、非退化単体の正則 pairing へ移すデータ。 -/
def edgewiseSupportPairEquiv (n : ℕ) : EdgewiseLowerSupport n ≃ EdgewiseUpperSupport n where
  toFun := edgewiseSupportRaise
  invFun := edgewiseSupportLower
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    change (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property))
      S.val.val).erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot
        (edgewiseSupportRaise S).val.val (edgewiseSupportRaise S).val.property)) = S.val.val
    rw [edgewiseSupportRaise_pivot, Finset.erase_insert S.property]
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    change insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot
        (edgewiseSupportLower S).val.val (edgewiseSupportLower S).val.property))
      (S.val.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S.val.val S.val.property))) = S.val.val
    rw [edgewiseSupportLower_pivot, Finset.insert_erase S.property]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
