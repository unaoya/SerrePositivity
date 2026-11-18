module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ContextBlockSwap

/-!
模型。文献の定義との比較は後で
# 前方を固定する二ブロック交換の尾への分離

概要：Berger–Moerdijk §1 の隣接入力の交換の出力を、前方の恒等全単射と尾の交換へ分解する。
方針：尾の二ブロック交換を定義し、有限直和の左右の成分で前方の分離を比較する。
規約：尾では a,b のブロックの後に元の未代入入力 q 個を置く。
使われ方：反復合成の残りの前方入力へ帰納するとき、尾の置換として外側等変性を適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：未代入入力を後方に残した尾の二ブロックを交換する（Berger–Moerdijk §1）。
方針：二ブロックの標準交換と後方の恒等全単射のブロック和を使う。
規約：arity の表記は q+a+b から q+b+a へ移す。
使われ方：代入後の残りの反復合成で尾に適用する全単射となる。 -/
def operadTailBlockSwap (q a b : ℕ) : Fin ((q + a) + b) ≃ Fin ((q + b) + a) :=
  (finCongr (by omega : (q + a) + b = (a + b) + q)).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b) (Equiv.refl (Fin q))).trans
      (finCongr (by omega : (b + a) + q = (q + b) + a)))

/-- 概要：前後を固定するブロック交換は前方の恒等全単射と尾の交換へ分解できる（Berger–Moerdijk §1）。
方針：前方の入力と残りの入力に分け、長さの移送とブロック全単射を計算する。
規約：前方 p 個を分離し、残りの長さを q+a+b とする。
使われ方：反復合成の残りの前方入力に、尾の置換の等変性を適用する。 -/
lemma operadContextBlockSwap_tail (p q a b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b =
      (finCongr (by omega : ((p + q) + a) + b = p + ((q + a) + b))).trans
        ((_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin p)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap q a b)).trans
          (finCongr (by omega : p + ((q + b) + a) = ((p + q) + b) + a))) := by
  let hs : ((p + q) + a) + b = p + ((q + a) + b) := by omega
  have hcancel (y : Fin (p + ((q + a) + b))) :
      finCongr hs (finCongr hs.symm y) = y := by apply Fin.ext; rfl
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (finCongr hs.symm).surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  cases y with
  | inl z =>
    simp only [finSumFinEquiv_apply_left]
    have he : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
        (finCongr hs.symm (z.castAdd ((q + a) + b))) = z.castAdd ((a + b) + q) := by
      apply Fin.ext; rfl
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
    rw [he, hcancel, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left]
    apply Fin.ext
    rfl
  | inr z =>
    simp only [finSumFinEquiv_apply_right]
    have he : finCongr (by omega : ((p + q) + a) + b = p + ((a + b) + q))
        (finCongr hs.symm (z.natAdd p)) =
          (finCongr (by omega : (q + a) + b = (a + b) + q) z).natAdd p := by
      apply Fin.ext; rfl
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply]
    rw [he, hcancel, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right]
    apply Fin.ext
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
