module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineRank
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewisePairingProper

/-!
概要：可算 spine の外の有限頂点集合の pairing を、元の非退化単体の pairing へ移す。
方針：全頂点集合の全単射を領域外へ制限し、最小番号の次の頂点を挿入する。
規約：元の可算 nerve の次元・面関係を保持する。
使われ方：P-11 の可算 spine の正則な inner horn 接合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：spine の外の非退化単体と、spine の外の有限頂点集合の全単射。
方針：全頂点集合の全単射を、spine 所属の同値で制限する。
規約：次元を含む元の単体の型を使う。
使われ方：有限集合の pairing の輸送。 -/
def sequentialSpineOutsideSimplexEquiv :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.N ≃ {S : Finset ℕ // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S} :=
  Equiv.ofBijective
    (fun s ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN, fun h ↦
      s.notMem ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerve_mem_spine_iff_support s.toN).mpr h)⟩) (by
      constructor
      · intro s t h
        exact (Subcomplex.N.ext_iff s t).mpr
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_injective (congrArg Subtype.val h))
      · intro S
        let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineOutside_nonempty S.property
        let x := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupportEquiv.{u}.symm ⟨S.val, hs⟩
        have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport x = S.val := congrArg Subtype.val
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupportEquiv.{u}.apply_symm_apply ⟨S.val, hs⟩)
        have hout : x.simplex ∉ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.obj _ := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerve_mem_spine_iff_support, hx]
          exact S.property
        exact ⟨Subcomplex.N.mk' x hout, Subtype.ext hx⟩)

/-- 概要：挿入点を欠く領域外の単体を、同じ条件の頂点集合へ移す。
方針：領域外の全単射を挿入点の不在条件で制限する。
規約：元の頂点集合を保持する。
使われ方：pairing の小さい方の座標。 -/
def sequentialSpineLowerSimplexEquiv :
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.N // _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN) ∉
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN} ≃
    {S : Finset ℕ // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S ∉ S} where
  toFun s := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN,
    (sequentialSpineOutsideSimplexEquiv.{u} s.val).property, s.property⟩
  invFun S := ⟨sequentialSpineOutsideSimplexEquiv.{u}.symm ⟨S.val, S.property.1⟩, by
    have hx := congrArg Subtype.val
      (sequentialSpineOutsideSimplexEquiv.{u}.apply_symm_apply ⟨S.val, S.property.1⟩)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport (sequentialSpineOutsideSimplexEquiv.{u}.symm
      ⟨S.val, S.property.1⟩).toN = S.val at hx
    rw [hx]
    exact S.property.2⟩
  left_inv s := Subtype.ext (sequentialSpineOutsideSimplexEquiv.{u}.symm_apply_apply s.val)
  right_inv S := by
    apply Subtype.ext
    have hx := congrArg Subtype.val
      (sequentialSpineOutsideSimplexEquiv.{u}.apply_symm_apply ⟨S.val, S.property.1⟩)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport (sequentialSpineOutsideSimplexEquiv.{u}.symm
      ⟨S.val, S.property.1⟩).toN = S.val at hx
    exact hx

/-- 概要：挿入点を含む領域外の単体を、同じ条件の頂点集合へ移す。
方針：領域外の全単射を挿入点の所属条件で制限する。
規約：元の頂点集合を保持する。
使われ方：pairing の大きい方の座標。 -/
def sequentialSpineUpperSimplexEquiv :
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.N // _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN) ∈
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN} ≃
    {S : Finset ℕ // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot S ∈ S} where
  toFun s := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN,
    (sequentialSpineOutsideSimplexEquiv.{u} s.val).property, s.property⟩
  invFun S := ⟨sequentialSpineOutsideSimplexEquiv.{u}.symm ⟨S.val, S.property.1⟩, by
    have hx := congrArg Subtype.val
      (sequentialSpineOutsideSimplexEquiv.{u}.apply_symm_apply ⟨S.val, S.property.1⟩)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport (sequentialSpineOutsideSimplexEquiv.{u}.symm
      ⟨S.val, S.property.1⟩).toN = S.val at hx
    rw [hx]
    exact S.property.2⟩
  left_inv s := Subtype.ext (sequentialSpineOutsideSimplexEquiv.{u}.symm_apply_apply s.val)
  right_inv S := by
    apply Subtype.ext
    have hx := congrArg Subtype.val
      (sequentialSpineOutsideSimplexEquiv.{u}.apply_symm_apply ⟨S.val, S.property.1⟩)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport (sequentialSpineOutsideSimplexEquiv.{u}.symm
      ⟨S.val, S.property.1⟩).toN = S.val at hx
    exact hx

/-- 概要：spine の外の単体で、挿入点を含むものと欠くものを対にする。
方針：領域外の頂点集合の全単射を、挿入点の有無でさらに制限する。
規約：同じ頂点集合上の挿入・削除の全単射を再利用する。
使われ方：元の可算 nerve の非退化単体の pairing。 -/
def sequentialSpinePairing : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.Pairing where
  I := fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN) ∈
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN
  II := fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN) ∉
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.toN
  inter := by ext s; change (_ ∧ ¬ _) ↔ False; tauto
  union := by
    classical
    ext s
    change (_ ∨ ¬ _) ↔ True
    tauto
  p := sequentialSpineLowerSimplexEquiv.{u}.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportPairEquiv.trans sequentialSpineUpperSimplexEquiv.{u}.symm)

/-- 概要：pairing の大きい単体の頂点集合は、小さい方へ選んだ一点を挿入したもの。
方針：頂点集合の全単射とその逆の合成を計算する。
規約：実際の有限集合の等式。
使われ方：面関係・次元差・inner 条件の共通入力。 -/
lemma sequentialSpinePairing_support (s : sequentialSpinePairing.{u}.II) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport (sequentialSpinePairing.{u}.p s).val.toN =
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN) := by
  have he := sequentialSpineUpperSimplexEquiv.{u}.apply_symm_apply
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportPairEquiv (sequentialSpineLowerSimplexEquiv.{u} s))
  exact congrArg Subtype.val he

/-- 概要：pairing の小さい単体は大きい方の面。
方針：頂点集合の包含を元の可算 nerve の面関係へ戻す。
規約：部分複体の外の元の単体を比較する。
使われ方：一意な余次元一の面の判定。 -/
lemma sequentialSpinePairing_le (s : sequentialSpinePairing.{u}.II) :
    s.val ≤ (sequentialSpinePairing.{u}.p s).val := by
  apply Subcomplex.N.le_iff.mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_subset_iff _ _).mp
  rw [sequentialSpinePairing_support]
  exact Finset.subset_insert _ _

/-- 概要：pairing は非退化単体の次元を一つ増やす。
方針：挿入点を欠く条件と頂点数の式を使う。
規約：本当に新しい一点を追加する。
使われ方：余次元一の面の一意性。 -/
lemma sequentialSpinePairing_dim (s : sequentialSpinePairing.{u}.II) :
    (sequentialSpinePairing.{u}.p s).val.dim = s.val.dim + 1 := by
  have h := congrArg Finset.card (sequentialSpinePairing_support s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_card, Finset.card_insert_of_notMem s.property,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_card] at h
  exact Nat.add_right_cancel h

/-- 概要：可算 spine の pairing は一意な余次元一の面を対応させる。
方針：poset nerve の非特異性、面関係、次元差一を既存の判定へ渡す。
規約：正則性の整礎条件は別工程。
使われ方：正則な inner horn 接合の proper 条件。 -/
instance sequentialSpinePairing_isProper : sequentialSpinePairing.{u}.IsProper where
  isUniquelyCodimOneFace s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.uniquelyCodimOneFace_of_nonsingular_le s.val.toN
    (sequentialSpinePairing.{u}.p s).val.toN
    (sequentialSpinePairing_le s) (sequentialSpinePairing_dim s)

/-- 概要：pairing の祖先関係は有限頂点集合の辞書式順位を厳密に下げる。
方針：面関係を頂点集合の包含へ移し、構成した順位比較を適用する。
規約：異なる対への面関係だけを比較する。
使われ方：全可算 spine に対する整礎性。 -/
lemma sequentialSpinePairing_ancestral_rank_lt (s t : sequentialSpinePairing.{u}.II)
    (hst : sequentialSpinePairing.{u}.AncestralRel s t) :
    Prod.Lex (· < ·) (· < ·)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportRank (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportRank (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport t.val.toN)) := by
  have hsub := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_subset_iff s.val.toN
    (sequentialSpinePairing.{u}.p t).val.toN).mpr hst.2.le
  rw [sequentialSpinePairing_support] at hsub
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportRank_lt _ _
    (sequentialSpineOutsideSimplexEquiv.{u} s.val).property
    (sequentialSpineOutsideSimplexEquiv.{u} t.val).property hsub s.property
  intro he
  apply hst.1
  exact Subtype.ext ((Subcomplex.N.ext_iff _ _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport_injective he))

/-- 概要：可算 spine の pairing は正則。
方針：自然数対の辞書式整礎性を祖先関係へ引き戻す。
規約：有限な spine への制限を仮定しない。
使われ方：全体の包含の inner anodyne 性への入口。 -/
instance sequentialSpinePairing_isRegular : sequentialSpinePairing.{u}.IsRegular where
  isUniquelyCodimOneFace := sequentialSpinePairing_isProper.isUniquelyCodimOneFace
  wf := by
    let r : sequentialSpinePairing.{u}.II → ℕ × ℕ :=
      fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineSupportRank (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s.val.toN)
    refine (InvImage.wf r (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)).mono ?_
    intro s t hst
    exact sequentialSpinePairing_ancestral_rank_lt s t hst

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
